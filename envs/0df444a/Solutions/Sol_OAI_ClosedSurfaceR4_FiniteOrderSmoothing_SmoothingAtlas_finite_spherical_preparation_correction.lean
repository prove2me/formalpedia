-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:46:45.612214+00:00
-- url     : https://prove2.me/submissions/3d3cc59f-b21a-4d01-9925-ed9cfaf3fd41

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FinitePointChartBalls
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily small disjoint coordinate balls around a prescribed finite
set. Their closed supports remain inside the supplied chart neighborhoods. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem finite_point_chart_balls {M : Type*} [TopologicalSpace M] [T2Space M]
    (P : Finset M) (e : P → OpenPartialHomeomorph M Plane)
    (he : ∀ p, (p : M) ∈ (e p).source) (U : P → Set M)
    (hU : ∀ p, IsOpen (U p)) (hpU : ∀ p, (p : M) ∈ U p)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : P → ℝ, (∀ p, 0 < r p ∧ r p < η ∧
      closedBall (e p p) (r p) ⊆ (e p).target ∩ (e p).symm ⁻¹' U p) ∧
      Pairwise (fun p q => Disjoint ((e p).symm '' closedBall (e p p) (r p))
        ((e q).symm '' closedBall (e q q) (r q))) := by
  classical
  obtain ⟨V,hV,hdisj⟩ := P.finite_toSet.t2_separation
  have hex (p : P) : ∃ r : ℝ, 0 < r ∧ r < η ∧
      closedBall (e p p) r ⊆ (e p).target ∩ (e p).symm ⁻¹' (U p ∩ V p) := by
    have ho := (e p).isOpen_inter_preimage_symm ((hU p).inter (hV p).2)
    have hp : e p p ∈ (e p).target ∩ (e p).symm ⁻¹' (U p ∩ V p) := by
      refine ⟨(e p).map_source (he p),?_⟩
      change (e p).symm (e p p) ∈ U p ∩ V p
      rw [(e p).left_inv (he p)]
      exact ⟨hpU p,(hV p).1⟩
    obtain ⟨r,hr,hrsub⟩ := nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hp)
    refine ⟨min r (η/2),lt_min hr (half_pos hη),?_,?_⟩
    · exact (min_le_right r (η/2)).trans_lt (half_lt_self hη)
    · exact (closedBall_subset_closedBall (min_le_left r (η/2))).trans hrsub
  choose r hr hrη hrsub using hex
  refine ⟨r,fun p => ⟨hr p,hrη p,?_⟩,?_⟩
  · intro x hx
    exact ⟨(hrsub p hx).1,(hrsub p hx).2.1⟩
  · intro p q hpq
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
    have hpV := (hrsub p hy).2.2
    have hqV := (hrsub q hz).2.2
    exact Set.disjoint_left.mp (hdisj p.property q.property
      (fun hpq' => hpq (Subtype.ext hpq'))) hpV (heq ▸ hqV)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EuclideanRestoration
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore a compactly supported Euclidean chart correction. The support
and germ formulas are used in finite-point spherical preparation. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma euclideanRestore_eq (p : M) (χ : M → ℝ) (h : Plane → Space) :
    euclideanRestore p χ h = (chartAt Plane p).source.indicator
      (fun x => χ x • h (chartAt Plane p x)) := by
  funext x
  by_cases hx : x ∈ (chartAt Plane p).source
  · simp [euclideanRestore,restore,chart,hx]
  · simp [euclideanRestore,restore,chart,hx]

lemma euclideanRestore_smooth [IsManifold planeModel ∞ M] (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hχs : tsupport χ ⊆ (chartAt Plane p).source) {h : Plane → Space}
    (hh : ContDiff ℝ ∞ h) : ContMDiff planeModel spaceModel ∞ (euclideanRestore p χ h) := by
  exact restore_smooth p hχ (by simpa only [chart_source] using hχs)
    (hh.comp (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff)

lemma euclideanRestore_tsupport [T2Space M] (p : M) (χ : M → ℝ) {h : Plane → Space}
    {K : Set Plane} (hK : IsCompact K) (hKt : K ⊆ (chartAt Plane p).target)
    (hs : tsupport h ⊆ K) :
    tsupport (euclideanRestore p χ h) ⊆ (chartAt Plane p).symm '' K := by
  have hclosed : IsClosed ((chartAt Plane p).symm '' K) :=
    (hK.image_of_continuousOn ((chartAt Plane p).continuousOn_symm.mono hKt)).isClosed
  apply closure_minimal _ hclosed
  intro x hx
  by_contra hn
  rw [euclideanRestore_eq] at hx
  by_cases hxs : x ∈ (chartAt Plane p).source
  · have hh : h (chartAt Plane p x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hn ⟨chartAt Plane p x,hs hmem,(chartAt Plane p).left_inv hxs⟩
    exact hx (by simp [indicator_of_mem hxs,hh])
  · exact hx (indicator_of_notMem hxs _)

lemma euclideanRestore_chart_germ (p : M) (χ : M → ℝ) (h : Plane → Space)
    {x : Plane} (hx : x ∈ (chartAt Plane p).target)
    (hχ : (fun y => χ ((chartAt Plane p).symm y)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    (fun y => euclideanRestore p χ h ((chartAt Plane p).symm y)) =ᶠ[𝓝 x] h := by
  filter_upwards [(chartAt Plane p).open_target.mem_nhds hx,hχ] with y hy hχy
  rw [euclideanRestore_eq,indicator_of_mem ((chartAt Plane p).map_target hy),
    hχy,one_smul,(chartAt Plane p).right_inv hy]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_EuclideanChartRead
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth Euclidean representatives agree with the actual chart map near
points where a partition weight is nonzero. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma euclideanChartRead_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.euclideanChartRead i F) :=
  (A.vectorChartRead_smooth i hF).comp (EuclideanSpace.equiv (Fin 2) ℝ).contDiff

omit [CompactSpace M] in
lemma euclideanChartRead_eq (i : A.centers) (F : M → Space) :
    A.euclideanChartRead i F = (chartAt Plane (i : M)).target.indicator
      (fun x => (A.outer i ((chartAt Plane (i : M)).symm x))^2 •
        F ((chartAt Plane (i : M)).symm x)) := by
  funext x
  by_cases hx : x ∈ (chartAt Plane (i : M)).target
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]
    rfl
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]

omit [CompactSpace M] in
lemma outer_one_chart_germ (i : A.centers) {p : M} (hp : A.weight i p ≠ 0) :
    (fun y => A.outer i ((chartAt Plane (i : M)).symm y)) =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      (fun _ => (1 : ℝ)) := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hpt := (chartAt Plane (i : M)).map_source hps
  have hc : ContinuousAt (fun y => A.weight i ((chartAt Plane (i : M)).symm y))
      (chartAt Plane (i : M) p) :=
    (A.weight_smooth i).continuous.continuousAt.comp
      (((chartAt Plane (i : M)).continuousOn_symm _ hpt).continuousAt
        ((chartAt Plane (i : M)).open_target.mem_nhds hpt))
  have hn : ∀ᶠ y in 𝓝 (chartAt Plane (i : M) p),
      A.weight i ((chartAt Plane (i : M)).symm y) ≠ 0 :=
    hc.eventually_ne (by simpa only [(chartAt Plane (i : M)).left_inv hps] using hp)
  exact hn.mono fun y hy => A.outer_one i _ (subset_tsupport _ hy)

omit [CompactSpace M] in
lemma euclideanChartRead_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.euclideanChartRead i F =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      F ∘ (chartAt Plane (i : M)).symm := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  filter_upwards [(chartAt Plane (i : M)).open_target.mem_nhds
    ((chartAt Plane (i : M)).map_source hps),A.outer_one_chart_germ i hp] with y hy ho
  rw [A.euclideanChartRead_eq,indicator_of_mem hy,ho,one_pow,one_smul]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The radial normal of a spherical surface immersion.  The identities are for
actual Fréchet derivatives and the orthogonal projection defining the second
fundamental form, not an abstract second-jet model.
-/

noncomputable section

open scoped ContDiff

namespace ClosedSurfaceR4.SphericalJets

lemma derivative_apply {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (x v w : Plane) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v =
      fderiv ℝ (fderiv ℝ F) x v w := by
  have hDF := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hDF (differentiableAt_const w)]
  simp

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedJetCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_smoothAt {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma radialNormalize_fderiv_unit {x : Space} (hx : ‖x‖ = 1) (v : Space) :
    fderiv ℝ radialNormalize x v = v - inner ℝ x v • x := by
  have hs := (hasFDerivAt_id x).norm_sq.sqrt (by simp [hx] : ‖x‖^2 ≠ 0)
  have hi := (hasDerivAt_inv (by simp [hx] : Real.sqrt (‖x‖^2) ≠ 0)).comp_hasFDerivAt x hs
  have hd := hi.smul (hasFDerivAt_id x)
  have he : (fun y : Space => (Real.sqrt (‖y‖^2))⁻¹ • y) = radialNormalize := by
    funext y
    simp [radialNormalize]
  change HasFDerivAt (fun y : Space => (Real.sqrt (‖y‖^2))⁻¹ • y) _ x at hd
  rw [he] at hd
  rw [hd.fderiv]
  simp [hx,ContinuousLinearMap.smulRight_apply,sub_eq_add_neg,neg_smul]

lemma secondDerivative_apply {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f : E → H} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ f q w) p v = fderiv ℝ (fderiv ℝ f) p v w := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (differentiableAt_const w)]
  simp

lemma secondDerivative_comp {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → H} {g : H → Z} {U : Set H} (hf : ContDiff ℝ ∞ f)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : f p ∈ U) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) p v w =
      fderiv ℝ (fderiv ℝ g) (f p) (fderiv ℝ f p v) (fderiv ℝ f p w) +
      fderiv ℝ g (f p) (fderiv ℝ (fderiv ℝ f) p v w) := by
  have hgp := hg.contDiffAt (hU.mem_nhds hp)
  have hDg := hgp.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := (hDg.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp p
    (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hD2 := (((hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (show ContDiff ℝ ∞ (fun _ : E => w) from contDiff_const)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hd := hD1.clm_apply hD2
  have he : (fun q => fderiv ℝ g (f q) (fderiv ℝ f q w)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (g ∘ f) q w) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    rw [fderiv_comp q ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q)]
    rfl
  have hev := congrArg (fun L : E →L[ℝ] Z => L v) (he.fderiv_eq.symm.trans hd.fderiv)
  rw [secondDerivative_apply (hgp.comp p hf.contDiffAt)] at hev
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    Function.comp_apply] at hev
  rw [secondDerivative_apply hf.contDiffAt] at hev
  simpa only [add_comm] using hev

/-- Maps with identical value and first derivative differ after radial
normalization by the differential of normalization applied to their
second-jet difference. -/
theorem radialNormalize_second_jet_difference {F G : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (p v w : Plane)
    (hFp : ‖F p‖ = 1) (hvalue : G p = F p)
    (hfirst : fderiv ℝ G p = fderiv ℝ F p) :
    fderiv ℝ (fderiv ℝ (radialNormalize ∘ G)) p v w -
      fderiv ℝ (fderiv ℝ (radialNormalize ∘ F)) p v w =
    (fderiv ℝ (fderiv ℝ G) p v w - fderiv ℝ (fderiv ℝ F) p v w) -
      inner ℝ (F p) (fderiv ℝ (fderiv ℝ G) p v w - fderiv ℝ (fderiv ℝ F) p v w) • F p := by
  have hne : F p ≠ 0 := by intro hz; simp [hz] at hFp
  have hU : IsOpen ({x : Space | x ≠ 0}) := isOpen_ne_fun continuous_id continuous_const
  have hn : ContDiffOn ℝ ∞ radialNormalize {x : Space | x ≠ 0} :=
    fun x hx => (radialNormalize_smoothAt hx).contDiffWithinAt
  rw [secondDerivative_comp hG hU hn (by change G p ≠ 0; rw [hvalue]; exact hne),
    secondDerivative_comp hF hU hn hne,hvalue,hfirst]
  have he : ∀ a b c : Space, (a+b)-(a+c) = b-c := fun a b c => by abel
  rw [he,← map_sub,radialNormalize_fderiv_unit hFp]

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticJetCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local quadratic correction in the finite-point spherical preparation.
The cutoff leaves its prescribed second jet unchanged. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma quadraticCorrection_smooth (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane) :
    ContDiff ℝ ∞ (quadraticCorrection B p) := by
  unfold quadraticCorrection
  exact ((B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
    (contDiff_id.sub contDiff_const)).const_smul _

lemma quadraticCorrection_fderiv (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (hB : ∀ v w, B v w = B w v) (p x : Plane) :
    fderiv ℝ (quadraticCorrection B p) x = - B (x-p) := by
  have hd := (B.hasFDerivAt_of_bilinear ((hasFDerivAt_id x).sub_const p)
    ((hasFDerivAt_id x).sub_const p)).const_smul (- (1 / 2 : ℝ))
  change HasFDerivAt (quadraticCorrection B p) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change (- (1/2 : ℝ)) • (B (x-p) v + B v (x-p)) = -(B (x-p) v)
  rw [hB v (x-p)]
  module

lemma quadraticCorrection_second (B : Plane →L[ℝ] Plane →L[ℝ] Space)
    (hB : ∀ v w, B v w = B w v) (p x v w : Plane) :
    fderiv ℝ (fderiv ℝ (quadraticCorrection B p)) x v w = - B v w := by
  have he : fderiv ℝ (quadraticCorrection B p) = fun x => -B (x-p) :=
    funext (quadraticCorrection_fderiv B hB p)
  rw [he]
  have hd := (B.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p)).neg
  change HasFDerivAt (fun x => -B (x-p)) _ x at hd
  rw [hd.fderiv]
  simp

lemma cutoffQuadratic_smooth (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) : ContDiff ℝ ∞ (cutoffQuadratic B p χ) :=
  χ.contDiff.smul (quadraticCorrection_smooth B p)

lemma cutoffQuadratic_germ (B : Plane →L[ℝ] Plane →L[ℝ] Space) (p : Plane)
    (χ : ContDiffBump p) : cutoffQuadratic B p χ =ᶠ[𝓝 p] quadraticCorrection B p := by
  filter_upwards [χ.eventuallyEq_one] with x hx
  simp [cutoffQuadratic, hx]

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalPointFlattening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact spherical second-jet cancellation by a supported quadratic map. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma sphericalSecondFormCLM_apply (F : Plane → Space) (p v w : Plane) :
    sphericalSecondFormCLM F p v w = sphericalSecondForm F p v w := rfl

lemma sphericalSecondForm_symmetric {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (p v w : Plane) : sphericalSecondForm F p v w = sphericalSecondForm F p w v := by
  unfold sphericalSecondForm secondForm
  rw [hF.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) v w,real_inner_comm]

lemma secondDerivative_add {F Q : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) (p v w : Plane) :
    fderiv ℝ (fderiv ℝ (F+Q)) p v w =
      fderiv ℝ (fderiv ℝ F) p v w + fderiv ℝ (fderiv ℝ Q) p v w := by
  have he : fderiv ℝ (F+Q) = fderiv ℝ F + fderiv ℝ Q := by
    funext x
    exact fderiv_add (hF.differentiable (by simp) x) (hQ.differentiable (by simp) x)
  rw [he, fderiv_add
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)
    ((hQ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p)]
  rfl

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalTensorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical correction tensor is bounded using only the first two
derivatives, uniformly without choosing a normal frame. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

lemma norm_sphericalSecondFormCLM_le (F : Plane → Space) (p : Plane) :
    ‖sphericalSecondFormCLM F p‖ ≤ ‖fderiv ℝ (fderiv ℝ F) p‖ +
      ‖fderiv ℝ F p‖^2 * ‖F p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [sphericalSecondFormCLM_apply,sphericalSecondForm]
  calc
    _ ≤ ‖secondForm F p v w‖ +
        ‖inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) • F p‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) p v w‖ +
        (‖fderiv ℝ F p v‖ * ‖fderiv ℝ F p w‖) * ‖F p‖ := by
      apply add_le_add
      · exact (normalSpace F p).norm_starProjection_apply_le _
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖fderiv ℝ (fderiv ℝ F) p‖ * ‖v‖ * ‖w‖ +
        ((‖fderiv ℝ F p‖ * ‖v‖) * (‖fderiv ℝ F p‖ * ‖w‖)) * ‖F p‖ := by
      apply add_le_add
      · exact ContinuousLinearMap.le_opNorm₂ _ _ _
      · gcongr
        · exact (fderiv ℝ F p).le_opNorm v
        · exact (fderiv ℝ F p).le_opNorm w
    _ = (‖fderiv ℝ (fderiv ℝ F) p‖ + ‖fderiv ℝ F p‖^2 * ‖F p‖) * ‖v‖ * ‖w‖ := by ring

lemma norm_sphericalSecondFormCLM_of_bounds {F : Plane → Space} {p : Plane}
    {C₁ C₂ : ℝ} (h₁ : ‖fderiv ℝ F p‖ ≤ C₁) (h₂ : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C₂)
    (hp : ‖F p‖ = 1) : ‖sphericalSecondFormCLM F p‖ ≤ C₂+C₁^2 := by
  apply (norm_sphericalSecondFormCLM_le F p).trans
  rw [hp,mul_one]
  gcongr

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasSphericalTensorBound
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tensors used for every finite-point correction have one bound,
fixed by the original immersion and its finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma euclideanChartRead_compact (i : A.centers) (F : M → Space) :
    HasCompactSupport (A.euclideanChartRead i F) :=
  (localize_compact (i : M) (A.outer_support i) F).comp_homeomorph
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph

theorem uniform_spherical_correction_tensor {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : A.centers) (p : M), A.weight i p ≠ 0 →
      ‖sphericalSecondFormCLM (A.euclideanChartRead i F) (chartAt Plane (i : M) p)‖ ≤ K := by
  classical
  have hb (i : A.centers) : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : M, A.weight i p ≠ 0 →
      ‖sphericalSecondFormCLM (A.euclideanChartRead i F) (chartAt Plane (i : M) p)‖ ≤ K := by
    let f := A.euclideanChartRead i F
    have hf := A.euclideanChartRead_smooth i hF
    have hc := A.euclideanChartRead_compact i F
    have hd := hf.fderiv_right (m := ∞) (by simp)
    have hdd := hd.fderiv_right (m := ∞) (by simp)
    obtain ⟨C₁,h₁⟩ := hd.continuous.bounded_above_of_compact_support (hc.fderiv ℝ)
    obtain ⟨C₂,h₂⟩ := hdd.continuous.bounded_above_of_compact_support ((hc.fderiv ℝ).fderiv ℝ)
    have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (h₁ 0)
    have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (h₂ 0)
    refine ⟨C₂+C₁^2,by positivity,?_⟩
    intro p hp
    apply norm_sphericalSecondFormCLM_of_bounds (h₁ _) (h₂ _)
    have he := (A.euclideanChartRead_germ i F hp).eq_of_nhds
    have hps : p ∈ (chartAt Plane (i : M)).source := by
      simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
    simp only [Function.comp_apply,(chartAt Plane (i : M)).left_inv hps] at he
    exact (congrArg norm he).trans (hunit p)
  choose K hK hb using hb
  refine ⟨∑ i, K i,Finset.sum_nonneg (fun i _ => hK i),?_⟩
  intro i p hp
  exact (hb i p hp).trans (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QuadraticCutoffBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform scale bounds for the local quadratic corrections.  The fixed
cutoff operator makes the constants independent of the tensor and radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.linearNormed
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.linearSpace
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.evalNormed
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.evalSpace
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.evTensorNormed
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.evTensorSpace
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.tensorNormed
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.tensorSpace
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.operatorNormed
attribute [local instance] OAI.ClosedSurfaceR4.SphericalJets.operatorSpace
lemma quadraticCutoffOperator_apply (x : Plane) (B : SecondTensor) :
    quadraticCutoffOperator x B = cutoffQuadratic B 0 unitJetCutoff x := by
  simp [quadraticCutoffOperator,cutoffQuadratic,quadraticCorrection,smul_smul,mul_comm]

lemma quadraticCutoffOperator_smooth : ContDiff ℝ ∞ quadraticCutoffOperator := by
  let ev₁ : Plane →L[ℝ] ((Plane →L[ℝ] Space) →L[ℝ] Space) := ContinuousLinearMap.apply ℝ Space
  have h₁ : ContDiff ℝ ∞ (fun x : Plane =>
      (ContinuousLinearMap.apply ℝ Space x : (Plane →L[ℝ] Space) →L[ℝ] Space)) := by
    exact ev₁.contDiff
  let ev₂ : Plane →L[ℝ] (SecondTensor →L[ℝ] (Plane →L[ℝ] Space)) :=
    ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space)
  have h₂ : ContDiff ℝ ∞ (fun x : Plane =>
      (ContinuousLinearMap.apply ℝ (Plane →L[ℝ] Space) x : SecondTensor →L[ℝ] (Plane →L[ℝ] Space))) := by
    exact ev₂.contDiff
  exact (contDiff_const.mul unitJetCutoff.contDiff).smul (h₁.clm_comp h₂)

lemma quadraticCutoffOperator_compact : HasCompactSupport quadraticCutoffOperator := by
  apply unitJetCutoff.hasCompactSupport.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp [quadraticCutoffOperator,hx]

theorem uniform_quadratic_cutoff_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ B : SecondTensor, ∀ j ≤ 2, ∀ x : Plane,
      ‖iteratedFDeriv ℝ j (cutoffQuadratic B 0 unitJetCutoff) x‖ ≤ C*‖B‖ := by
  obtain ⟨C,hC,hb⟩ := quadraticCutoffOperator_compact.exists_bound_iteratedFDeriv (𝕜 := ℝ)
    quadraticCutoffOperator_smooth 2
  refine ⟨C,hC,?_⟩
  intro B j hj x
  have he : cutoffQuadratic B 0 unitJetCutoff = fun y => quadraticCutoffOperator y B := by
    funext y
    exact (quadraticCutoffOperator_apply y B).symm
  rw [he]
  calc
    _ ≤ ‖B‖*‖iteratedFDeriv ℝ j quadraticCutoffOperator x‖ :=
      norm_iteratedFDeriv_clm_apply_const quadraticCutoffOperator_smooth.contDiffAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    _ ≤ ‖B‖*C := mul_le_mul_of_nonneg_left (hb j hj x) (norm_nonneg _)
    _ = C*‖B‖ := mul_comm _ _

lemma scaledQuadraticCutoff_smooth (B : SecondTensor) (p : Plane) (r : ℝ) :
    ContDiff ℝ ∞ (scaledQuadraticCutoff B p r) :=
  ((cutoffQuadratic_smooth B 0 unitJetCutoff).comp
    ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul (r^2)

lemma scaledQuadraticCutoff_germ (B : SecondTensor) (p : Plane) {r : ℝ} (hr : 0 < r) :
    scaledQuadraticCutoff B p r =ᶠ[𝓝 p] quadraticCorrection B p := by
  have hc : Continuous (fun x : Plane => r⁻¹ • (x-p)) := by fun_prop
  have ht : Tendsto (fun x : Plane => r⁻¹ • (x-p)) (𝓝 p) (𝓝 0) := by
    simpa only [sub_self,smul_zero] using hc.continuousAt.tendsto (x := p)
  have he := (cutoffQuadratic_germ B 0 unitJetCutoff).comp_tendsto ht
  filter_upwards [he] with x hx
  simp only [Function.comp_apply] at hx
  unfold scaledQuadraticCutoff
  rw [hx]
  simp only [quadraticCorrection,sub_zero,map_smul,smul_apply,smul_smul]
  congr 1
  field_simp [hr.ne']

lemma scaledQuadraticCutoff_tsupport (B : SecondTensor) (p : Plane) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledQuadraticCutoff B p r) ⊆ closedBall p r := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hball
  have hn : r ≤ ‖x-p‖ := (not_le.mp (by simpa only [mem_closedBall_iff_norm] using hball)).le
  have hd : 1 ≤ dist (r⁻¹ • (x-p)) 0 := by
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    simpa only [div_eq_inv_mul] using (one_le_div hr).mpr hn
  have hz := unitJetCutoff.zero_of_le_dist hd
  simp [scaledQuadraticCutoff,cutoffQuadratic,hz] at hx

lemma scaledQuadraticCutoff_norm_deriv (B : SecondTensor) (p : Plane) {r : ℝ}
    (hr : 0 < r) (j : ℕ) (x : Plane) :
    r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ =
      r^2 * ‖iteratedFDeriv ℝ j (cutoffQuadratic B 0 unitJetCutoff)
        (r⁻¹ • (x-p))‖ := by
  have hs := cutoffQuadratic_smooth B 0 unitJetCutoff
  have hc : ContDiff ℝ ∞ (fun x : Plane =>
      cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • (x-p))) :=
    hs.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  unfold scaledQuadraticCutoff
  rw [iteratedFDeriv_const_smul_apply' (hc.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt]
  rw [iteratedFDeriv_comp_sub (f := fun y => cutoffQuadratic B 0 unitJetCutoff (r⁻¹ • y)) j p x]
  rw [congrFun (iteratedFDeriv_comp_const_smul r⁻¹ (hs.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))) (x-p)]
  rw [norm_smul,norm_smul]
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r),abs_pow,abs_inv,abs_of_pos hr,
    inv_pow]
  field_simp [hr.ne']

/-- The three orders have sizes O(r²), O(r), O(1), with one constant for
all tensors and all positive radii. -/
theorem uniform_scaled_quadratic_bounds : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (B : SecondTensor) (p : Plane) (r : ℝ), 0 < r → ∀ j ≤ 2, ∀ x : Plane,
      r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ ≤ C*‖B‖*r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_quadratic_cutoff_bound
  refine ⟨C,hC,?_⟩
  intro B p r hr j hj x
  rw [scaledQuadraticCutoff_norm_deriv B p hr]
  nlinarith [hb B j hj (r⁻¹ • (x-p))]

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DisjointJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint supports prevent a factor counting the prescribed points in
the finite-point preparation estimates. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.SphericalJets
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem disjoint_sum_jet_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → E → V) (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hb : ∀ i ∈ s, ∀ x, ‖iteratedFDeriv ℝ j (q i) x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => ∑ i ∈ s, q i x) x‖ ≤ C := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hq i hi).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  have hz (i : ι) (hx : x ∉ tsupport (q i)) : iteratedFDeriv ℝ j (q i) x = 0 := by
    by_contra hn
    exact hx (tsupport_iteratedFDeriv_subset j (subset_closure hn))
  by_cases hex : ∃ i ∈ s, x ∈ tsupport (q i)
  · obtain ⟨i,hi,hxi⟩ := hex
    have hzero : ∀ k ∈ s, k ≠ i → iteratedFDeriv ℝ j (q k) x = 0 := by
      intro k hk hki
      apply hz k
      exact fun hxk => Set.disjoint_left.mp (hdisj hk hi hki) hxk hxi
    rw [Finset.sum_eq_single i hzero (by simp [hi])]
    exact hb i hi x
  · have hzero : ∀ i ∈ s, iteratedFDeriv ℝ j (q i) x = 0 := by
      intro i hi
      exact hz i (fun hxi => hex ⟨i,hi,hxi⟩)
    rw [Finset.sum_eq_zero hzero,norm_zero]
    exact hC

theorem disjoint_sum_weighted_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → E → V) (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hb : ∀ i ∈ s, WeightedEstimates.WeightedBound univ 1 m C (q i)) :
    WeightedEstimates.WeightedBound univ 1 m C (fun x => ∑ i ∈ s, q i x) := by
  intro j hj x hx
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  apply disjoint_sum_jet_bound s q hq hdisj hC j
  intro i hi y
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hb i hi j hj y (mem_univ y)

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_DisjointAtlasBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed atlas retains the count-free estimate for a disjoint family
of local corrections. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem disjoint_weighted_sum_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → M → Space) (hq : ∀ i ∈ s, ContMDiff planeModel spaceModel ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hb : ∀ i ∈ s, A.WeightedBound 1 m C (q i)) :
    A.WeightedBound 1 m C (∑ i ∈ s, q i) := by
  intro a
  rw [localize_sum]
  have hloc : (↑s : Set ι).Pairwise fun i j =>
      Disjoint (tsupport (localize (a : M) (A.weight a) (q i)))
        (tsupport (localize (a : M) (A.weight a) (q j))) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨p,⟨hp,hpi⟩,hpx⟩ := localize_tsupport_inter (a : M) (A.weight_support a) (q i) hxi
    obtain ⟨r,⟨hr,hrj⟩,hrx⟩ := localize_tsupport_inter (a : M) (A.weight_support a) (q j) hxj
    have hpr : p = r := (chart (a : M)).injOn (A.weight_support a hp)
      (A.weight_support a hr) (hpx.trans hrx.symm)
    exact Set.disjoint_left.mp (hdisj hi hj hij) hpi (hpr.symm ▸ hrj)
  exact SphericalJets.disjoint_sum_weighted_bound s
    (fun i => localize (a : M) (A.weight a) (q i))
    (fun i hi => localize_smooth (a : M) (A.weight_smooth a) (A.weight_support a) (hq i hi))
    hloc hC (fun i hi => hb i hi a)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalJetGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local versions of the spherical identities. Chart representatives need
take values in the sphere only near the point under consideration. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma radial_first_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v : Plane) :
    inner ℝ (F p) (fderiv ℝ F p v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [hunit] with y hy
    rw [real_inner_self_eq_norm_sq,hy]
    norm_num
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v) he.fderiv_eq
  rw [fderiv_inner_apply ℝ (hF.differentiable (by simp) p)
    (hF.differentiable (by simp) p)] at hh
  simp only [fderiv_const_apply,zero_apply,real_inner_comm (F p)] at hh
  linarith

lemma radial_second_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v w : Plane) :
    inner ℝ (F p) (fderiv ℝ (fderiv ℝ F) p v w) =
      -inner ℝ (fderiv ℝ F p v) (fderiv ℝ F p w) := by
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) =ᶠ[𝓝 p]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hunit.eventually_nhds] with y hy
    exact radial_first_of_germ hF hy w
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v) he.fderiv_eq
  have hD := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p
  rw [fderiv_inner_apply ℝ (hF.differentiable (by simp) p)
    (hD.clm_apply (differentiableAt_const w)),derivative_apply hF] at hh
  simp only [fderiv_const_apply,zero_apply] at hh
  linarith

lemma radial_normal_mem_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) :
    F p ∈ normalSpace F p := by
  rw [normalSpace,Submodule.mem_orthogonal]
  rintro _ ⟨v,rfl⟩
  change inner ℝ (fderiv ℝ F p v) (F p) = 0
  rw [real_inner_comm]
  exact radial_first_of_germ hF hunit v

lemma sphericalSecondForm_mem_of_germ {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1) (v w : Plane) :
    sphericalSecondForm F p v w ∈ normalSpace F p := by
  exact Submodule.add_mem _ (Submodule.starProjection_apply_mem _ _)
    (Submodule.smul_mem _ _ (radial_normal_mem_of_germ hF hunit))

lemma sphericalSecondForm_radial_orthogonal_of_germ {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {p : Plane} (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1)
    (v w : Plane) : inner ℝ (sphericalSecondForm F p v w) (F p) = 0 := by
  have hp : ‖F p‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have hnorm : inner ℝ (F p) (F p) = 1 := by rw [real_inner_self_eq_norm_sq,hp]; norm_num
  rw [sphericalSecondForm,inner_add_left,real_inner_smul_left,hnorm,mul_one,
    secondForm,Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (radial_normal_mem_of_germ hF hunit),
    real_inner_comm,radial_second_of_germ hF hunit]
  exact neg_add_cancel _

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalizedSphericalGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local normalization calculation in a chart representative. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

theorem normalized_spherical_flattening {F Q : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q) {p : Plane}
    (hunit : ∀ᶠ x in 𝓝 p, ‖F x‖ = 1)
    (hq0 : Q p = 0) (hq1 : fderiv ℝ Q p = 0)
    (hq2 : ∀ v w, fderiv ℝ (fderiv ℝ Q) p v w = -sphericalSecondForm F p v w) :
    let G := radialNormalize ∘ (F+Q)
    G p = F p ∧ fderiv ℝ G p = fderiv ℝ F p ∧
      ∀ v w, sphericalSecondForm G p v w = 0 := by
  let H := F+Q
  let G := radialNormalize ∘ H
  have hp : ‖F p‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have hH : ContDiff ℝ ∞ H := hF.add hQ
  have hH0 : H p = F p := by change F p + Q p = F p; rw [hq0,add_zero]
  have hH1 : fderiv ℝ H p = fderiv ℝ F p := by
    rw [show H = F+Q from rfl, fderiv_add (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
      (hQ.differentiable (by simp) p),hq1,add_zero]
  have hn : F p ≠ 0 := by intro hz; simp [hz] at hp
  have hG0 : G p = F p := by simp [G,Function.comp_apply,hH0,radialNormalize,hp]
  have hG1 : fderiv ℝ G p = fderiv ℝ F p := by
    apply ContinuousLinearMap.ext
    intro v
    rw [show G = radialNormalize ∘ H from rfl,
      fderiv_comp p ((radialNormalize_smoothAt (by rw [hH0]; exact hn)).differentiableAt
        (by simp)) (hH.differentiable (by simp) p)]
    simp only [ContinuousLinearMap.comp_apply,hH0,hH1,
      radialNormalize_fderiv_unit hp,radial_first_of_germ hF hunit,zero_smul,sub_zero]
  have hN : normalSpace G p = normalSpace F p := by unfold normalSpace; rw [hG1]
  have hrad : radialNormalize ∘ F =ᶠ[𝓝 p] F := by
    filter_upwards [hunit] with x hx
    simp [radialNormalize,Function.comp_apply,hx]
  have hG2 (v w : Plane) : fderiv ℝ (fderiv ℝ G) p v w =
      fderiv ℝ (fderiv ℝ F) p v w - sphericalSecondForm F p v w := by
    have hd := radialNormalize_second_jet_difference hF hH p v w hp hH0 hH1
    rw [hrad.fderiv.fderiv_eq,secondDerivative_add hF hQ,hq2] at hd
    have hc : fderiv ℝ (fderiv ℝ F) p v w + -sphericalSecondForm F p v w -
        fderiv ℝ (fderiv ℝ F) p v w = -sphericalSecondForm F p v w := by abel
    have ho : inner ℝ (F p) (sphericalSecondForm F p v w) = 0 := by
      rw [real_inner_comm]
      exact sphericalSecondForm_radial_orthogonal_of_germ hF hunit v w
    rw [hc,inner_neg_right,ho,neg_zero,zero_smul,sub_zero] at hd
    exact sub_eq_iff_eq_add.mp hd |>.trans (by abel)
  refine ⟨hG0,hG1,?_⟩
  intro v w
  change (normalSpace G p).starProjection (fderiv ℝ (fderiv ℝ G) p v w) +
    inner ℝ (fderiv ℝ G p v) (fderiv ℝ G p w) • G p = 0
  simp only [hN,hG2,map_sub,hG1,hG0]
  rw [Submodule.starProjection_eq_self_iff.mpr (sphericalSecondForm_mem_of_germ hF hunit v w)]
  change secondForm F p v w - sphericalSecondForm F p v w + _ = 0
  unfold sphericalSecondForm
  abel

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteCorrectionGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite disjoint corrections retain each prescribed local jet. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma finite_sum_germ_of_disjoint_supports {E V ι : Type*}
    [TopologicalSpace E] [AddCommMonoid V] [DecidableEq ι]
    (s : Finset ι) (q : ι → E → V) (K : ι → Set E)
    (hs : ∀ i ∈ s, tsupport (q i) ⊆ K i)
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (K i) (K j))
    {i : ι} (hi : i ∈ s) {p : E} (hp : p ∈ K i) :
    (fun x => ∑ j ∈ s, q j x) =ᶠ[𝓝 p] q i := by
  have he : ∀ᶠ x in 𝓝 p, ∀ j ∈ s, j ≠ i → q j x = 0 := by
    apply (eventually_all_finset s).mpr
    intro j hj
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ hn => False.elim (hn hji)
    · have hnot : p ∉ tsupport (q j) := by
        intro hq
        exact Set.disjoint_left.mp (hdisj hj hi hji) (hs j hj hq) hp
      exact (notMem_tsupport_iff_eventuallyEq.mp hnot).mono (fun _ hx _ => hx)
  filter_upwards [he] with x hx
  exact Finset.sum_eq_single i (fun j hj hji => hx j hj hji) (by simp [hi])

lemma scaledQuadraticCutoff_jets (B : SecondTensor) (hB : ∀ v w, B v w = B w v)
    (p : Plane) {r : ℝ} (hr : 0 < r) :
    scaledQuadraticCutoff B p r p = 0 ∧
      fderiv ℝ (scaledQuadraticCutoff B p r) p = 0 ∧
      ∀ v w, fderiv ℝ (fderiv ℝ (scaledQuadraticCutoff B p r)) p v w = -B v w := by
  have he := scaledQuadraticCutoff_germ B p hr
  refine ⟨?_,?_,?_⟩
  · rw [he.eq_of_nhds]
    simp [quadraticCorrection]
  · rw [he.fderiv_eq,quadraticCorrection_fderiv B hB]
    simp
  · intro v w
    rw [he.fderiv.fderiv_eq,quadraticCorrection_second B hB]

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSurfaceCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical jet corrections on the actual surface. The disjoint
coordinate balls are chosen before restoring and normalizing the corrections. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma sphericalSecondForm_congr_germ {F G : Plane → Space} {p : Plane}
    (h : F =ᶠ[𝓝 p] G) (v w : Plane) :
    sphericalSecondForm F p v w = sphericalSecondForm G p v w := by
  simp only [sphericalSecondForm,secondForm,normalSpace,h.eq_of_nhds,h.fderiv_eq,
    h.fderiv.fderiv_eq]

end ClosedSurfaceR4.SphericalJets
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma finiteSurfaceQuadratic_smooth (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) :
    ContMDiff planeModel spaceModel ∞ (A.finiteSurfaceQuadratic P c r F) := by
  apply ContMDiff.sum
  intro p _
  exact euclideanRestore_smooth _ (A.outer_smooth _) (by simpa only [chart_source]
    using (A.outer_support (c p))) (scaledQuadraticCutoff_smooth _ _ _)

omit [CompactSpace M] in
lemma finiteSurfaceQuadratic_chart_germ (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) (hc : ∀ p, A.weight (c p) p ≠ 0) (hr : ∀ p, 0 < r p)
    (hball : ∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target)
    (hdisj : Pairwise fun p q : P =>
      Disjoint ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q)))
    (p : P) :
    (fun y => A.finiteSurfaceQuadratic P c r F ((chartAt Plane (c p : M)).symm y))
      =ᶠ[𝓝 (chartAt Plane (c p : M) p)]
      scaledQuadraticCutoff (sphericalSecondFormCLM (A.euclideanChartRead (c p) F)
        (chartAt Plane (c p : M) p)) (chartAt Plane (c p : M) p) (r p) := by
  classical
  let q (p : P) := scaledQuadraticCutoff
    (sphericalSecondFormCLM (A.euclideanChartRead (c p) F) (chartAt Plane (c p : M) p))
    (chartAt Plane (c p : M) p) (r p)
  let Q (p : P) := euclideanRestore (c p : M) (A.outer (c p)) (q p)
  let K (p : P) := (chartAt Plane (c p : M)).symm ''
    closedBall (chartAt Plane (c p : M) p) (r p)
  have hps : (p : M) ∈ (chartAt Plane (c p : M)).source := by
    simpa only [chart_source] using A.weight_support (c p) (subset_tsupport _ (hc p))
  have hpt := (chartAt Plane (c p : M)).map_source hps
  have hpK : (p : M) ∈ K p := ⟨chartAt Plane (c p : M) p,
    mem_closedBall_self (hr p).le,(chartAt Plane (c p : M)).left_inv hps⟩
  have he : A.finiteSurfaceQuadratic P c r F =ᶠ[𝓝 (p : M)] Q p :=
    finite_sum_germ_of_disjoint_supports Finset.univ Q K
      (fun q _ => euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (hball q)
        (scaledQuadraticCutoff_tsupport _ _ (hr q)))
      (fun p _ q _ hpq => hdisj hpq) (Finset.mem_univ p) hpK
  have ht : Tendsto (chartAt Plane (c p : M)).symm (𝓝 (chartAt Plane (c p : M) p))
      (𝓝 (p : M)) := by
    have hh := ((chartAt Plane (c p : M)).continuousOn_symm _ hpt).continuousAt
      ((chartAt Plane (c p : M)).open_target.mem_nhds hpt)
    simpa only [(chartAt Plane (c p : M)).left_inv hps] using hh.tendsto
  exact (he.comp_tendsto ht).trans
    (euclideanRestore_chart_germ _ _ _ hpt (A.outer_one_chart_germ (c p) (hc p)))

theorem finiteSurfaceQuadratic_flattening (P : Finset M) (c : P → A.centers) (r : P → ℝ)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (hunit : ∀ p, ‖F p‖ = 1) (hc : ∀ p, A.weight (c p) p ≠ 0) (hr : ∀ p, 0 < r p)
    (hball : ∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target)
    (hdisj : Pairwise fun p q : P =>
      Disjoint ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q))) :
    let G := radialNormalize ∘ (F + A.finiteSurfaceQuadratic P c r F)
    ∀ p : P, G p = F p ∧
      fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
        fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
      ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
        (chartAt Plane (c p : M) p) v w = 0 := by
  intro G p
  let x := chartAt Plane (c p : M) p
  let f := A.euclideanChartRead (c p) F
  let q := scaledQuadraticCutoff (sphericalSecondFormCLM f x) x (r p)
  have hf := A.euclideanChartRead_smooth (c p) hF
  have he := A.euclideanChartRead_germ (c p) F (hc p)
  have hu : ∀ᶠ y in 𝓝 x, ‖f y‖ = 1 :=
    he.mono fun y hy => (congrArg norm hy).trans (hunit _)
  obtain ⟨hq0,hq1,hq2⟩ := scaledQuadraticCutoff_jets (sphericalSecondFormCLM f x)
    (fun v w => sphericalSecondForm_symmetric hf x v w) x (hr p)
  obtain ⟨hg0,hg1,hg2⟩ := normalized_spherical_flattening hf
    (scaledQuadraticCutoff_smooth _ _ _) hu hq0 hq1 hq2
  have hq := A.finiteSurfaceQuadratic_chart_germ P c r F hc hr hball hdisj p
  have hg : G ∘ (chartAt Plane (c p : M)).symm =ᶠ[𝓝 x] radialNormalize ∘ (f+q) := by
    filter_upwards [he,hq] with y hy hqy
    change radialNormalize (F ((chartAt Plane (c p : M)).symm y) +
      A.finiteSurfaceQuadratic P c r F ((chartAt Plane (c p : M)).symm y)) = _
    simp only [Function.comp_apply] at hy
    rw [← hy,hqy]
    rfl
  have hps : (p : M) ∈ (chartAt Plane (c p : M)).source := by
    simpa only [chart_source] using A.weight_support (c p) (subset_tsupport _ (hc p))
  refine ⟨?_,hg.fderiv_eq.trans (hg1.trans he.fderiv_eq),?_⟩
  · have hv := hg.eq_of_nhds.trans (hg0.trans he.eq_of_nhds)
    simpa only [Function.comp_apply,x,(chartAt Plane (c p : M)).left_inv hps] using hv
  · intro v w
    exact (sphericalSecondForm_congr_germ hg v w).trans (hg2 v w)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledQuadraticBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C1 smallness and a radius-independent C2 budget for the actual scaled
quadratic corrections. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

theorem scaled_quadratic_C1_C2_budgets (K : ℝ) (hK : 0 ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (B : SecondTensor), ‖B‖ ≤ K →
      ∀ (p : Plane) (r : ℝ), 0 < r → r ≤ 1 →
        WeightedEstimates.WeightedBound univ 1 1 (D*r) (scaledQuadraticCutoff B p r) ∧
        WeightedEstimates.WeightedBound univ 1 2 D (scaledQuadraticCutoff B p r) := by
  obtain ⟨C,hC,hb⟩ := uniform_scaled_quadratic_bounds
  let D := C*K
  have hD : 0 ≤ D := mul_nonneg hC hK
  refine ⟨D,hD,?_⟩
  intro B hB p r hr hr1
  have hCK : C*‖B‖ ≤ D := mul_le_mul_of_nonneg_left hB hC
  have hbound (j : ℕ) (hj : j ≤ 2) (x : Plane) :
      r^j * ‖iteratedFDeriv ℝ j (scaledQuadraticCutoff B p r) x‖ ≤ D*r^2 := by
    exact (hb B p r hr j hj x).trans (mul_le_mul_of_nonneg_right hCK (sq_nonneg r))
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hrr : r^2 ≤ r := by nlinarith
  constructor
  · intro j hj x hx
    rw [iteratedFDerivWithin_univ]
    simp only [one_pow,one_mul]
    have hh := hbound j (by omega) x
    interval_cases j
    · simp only [pow_zero,one_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hrr hD)
    · simp only [pow_one] at hh
      nlinarith
  · intro j hj x hx
    rw [iteratedFDerivWithin_univ]
    simp only [one_pow,one_mul]
    have hh := hbound j hj x
    interval_cases j
    · simp only [pow_zero,one_mul] at hh
      exact hh.trans (by nlinarith [mul_nonneg hD (by nlinarith : 0 ≤ 1-r^2)])
    · simp only [pow_one] at hh
      nlinarith [mul_nonneg hD (by linarith : 0 ≤ 1-r)]
    · nlinarith

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SingleEuclideanRestoreBound
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed atlas controls a single Euclidean restored correction, with a
constant independent of its center, support radius and jet tensor. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem single_euclidean_restore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (i : A.centers) (f : Plane → Space) (C : ℝ),
      0 ≤ C → ContDiff ℝ ∞ f → WeightedEstimates.WeightedBound univ 1 m C f →
      A.WeightedBound 1 m (D*C) (euclideanRestore (i : M) (A.outer i) f) := by
  classical
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap
  let K : ℝ := max 1 ‖e‖ ^ m
  have hK : 0 ≤ K := pow_nonneg (le_max_of_le_left zero_le_one) _
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := Space) m
  refine ⟨D*K,mul_nonneg hD hK,?_⟩
  intro i f C hC hf hb
  have he : WeightedEstimates.WeightedBound univ 1 m (K*C) (f ∘ e) := by
    intro j hj x hx
    rw [iteratedFDerivWithin_univ,e.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
    simp only [one_pow,one_mul]
    have hnorm := (iteratedFDeriv ℝ j f (e x)).norm_compContinuousLinearMap_le
      (fun _ => e)
    have hp : ‖e‖^j ≤ K := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖e‖) _).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖e‖) hj)
    have hv := hb j hj (e x) (mem_univ _)
    simp only [iteratedFDerivWithin_univ,one_pow,one_mul] at hv
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f (e x)‖ * ∏ _ : Fin j, ‖e‖ := hnorm
      _ = ‖iteratedFDeriv ℝ j f (e x)‖ * ‖e‖^j := by simp
      _ ≤ C*K := mul_le_mul hv hp (pow_nonneg (norm_nonneg _) _) hC
      _ = K*C := mul_comm _ _
  have hr := hd (fun k => if k = i then f ∘ e else 0) 1 (K*C)
    zero_lt_one le_rfl (mul_nonneg hK hC)
    (fun k => by split_ifs; exact hf.comp e.contDiff; exact contDiff_const)
    (fun k => by split_ifs; exact he; exact (weightedBound_zero univ 1 m).mono_const (mul_nonneg hK hC))
  have heq : (∑ k : A.centers, restore (k : M) (A.outer k)
      (if k = i then f ∘ e else 0)) = euclideanRestore (i : M) (A.outer i) f := by
    funext p
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [euclideanRestore,e]
    · intro j _ hji
      simp [hji,restore]
    · simp
  rw [heq] at hr
  simpa only [mul_assoc] using hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSurfaceCorrectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total finite-point correction is arbitrarily small in C1 and
uniformly bounded in C2, independently of the finite set. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_surface_correction_budgets {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (c : P → A.centers) (r : P → ℝ) (η : ℝ),
      0 < η → η ≤ 1 → (∀ p, A.weight (c p) p ≠ 0) →
      (∀ p, 0 < r p ∧ r p ≤ η) →
      (∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆ (chartAt Plane (c p : M)).target) →
      (Pairwise fun p q : P => Disjoint
        ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q))) →
      A.WeightedBound 1 1 (D*η) (A.finiteSurfaceQuadratic P c r F) ∧
      A.WeightedBound 1 2 D (A.finiteSurfaceQuadratic P c r F) := by
  classical
  obtain ⟨K,hK,hKB⟩ := A.uniform_spherical_correction_tensor hF hunit
  obtain ⟨C,hC,hCB⟩ := scaled_quadratic_C1_C2_budgets K hK
  obtain ⟨D₁,hD₁,h₁⟩ := A.single_euclidean_restore_bound 1
  obtain ⟨D₂,hD₂,h₂⟩ := A.single_euclidean_restore_bound 2
  refine ⟨(D₁+D₂)*C,by positivity,?_⟩
  intro P c r η hη hη1 hc hr ht hd
  let q (p : P) := scaledQuadraticCutoff
    (sphericalSecondFormCLM (A.euclideanChartRead (c p) F) (chartAt Plane (c p : M) p))
    (chartAt Plane (c p : M) p) (r p)
  let Q (p : P) := euclideanRestore (c p : M) (A.outer (c p)) (q p)
  have hQs (p : P) : ContMDiff planeModel spaceModel ∞ (Q p) :=
    euclideanRestore_smooth _ (A.outer_smooth _) (by simpa only [chart_source]
      using (A.outer_support (c p))) (scaledQuadraticCutoff_smooth _ _ _)
  have hQd : (↑(Finset.univ : Finset P) : Set P).Pairwise
      fun p q => Disjoint (tsupport (Q p)) (tsupport (Q q)) := by
    intro p _ q _ hpq
    exact (hd hpq).mono
      (euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (ht p)
        (scaledQuadraticCutoff_tsupport _ _ (hr p).1))
      (euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (ht q)
        (scaledQuadraticCutoff_tsupport _ _ (hr q).1))
  have hbud (p : P) := hCB _ (hKB (c p) p (hc p)) (chartAt Plane (c p : M) p) (r p) (hr p).1 ((hr p).2.trans hη1)
  have hsum : A.finiteSurfaceQuadratic P c r F = ∑ p : P, Q p := by
    funext x
    simp only [Finset.sum_apply]
    rfl
  rw [hsum]
  constructor
  · apply A.disjoint_weighted_sum_bound Finset.univ Q (fun p _ => hQs p) hQd
      (mul_nonneg (mul_nonneg (add_nonneg hD₁ hD₂) hC) hη.le)
    intro p _ i
    apply (h₁ (c p) (q p) (C*r p) (mul_nonneg hC (hr p).1.le)
      (scaledQuadraticCutoff_smooth _ _ _) (hbud p).1 i).mono_const
    calc
      D₁*(C*r p) ≤ D₁*(C*η) := by gcongr; exact (hr p).2
      _ ≤ ((D₁+D₂)*C)*η := by nlinarith [mul_nonneg hD₂ (mul_nonneg hC hη.le)]
  · apply A.disjoint_weighted_sum_bound Finset.univ Q (fun p _ => hQs p) hQd
      (mul_nonneg (add_nonneg hD₁ hD₂) hC)
    intro p _ i
    apply (h₂ (c p) (q p) C hC (scaledQuadraticCutoff_smooth _ _ _) (hbud p).2 i).mono_const
    nlinarith [mul_nonneg hD₂ hC]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionApproximation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coreThreshold_pos : 0 < A.coreThreshold := by unfold coreThreshold; positivity

omit [CompactSpace M] in
lemma weightCore_nonzero (i : A.centers) {p : M} (hp : p ∈ A.weightCore i) :
    A.weight i p ≠ 0 := by
  intro hz
  have h := A.coreThreshold_pos
  change A.coreThreshold ≤ (A.weight i p)^2 at hp
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hp
  exact (not_lt_of_ge hp) h

omit [CompactSpace M] in
lemma mem_some_weightCore (p : M) : ∃ i : A.centers, p ∈ A.weightCore i := by
  classical
  by_contra hn
  have hi (i : A.centers) : (A.weight i p)^2 ≤ A.coreThreshold :=
    le_of_lt (lt_of_not_ge (fun h => hn ⟨i,h⟩))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset A.centers)) (fun i _ => hi i)
  rw [A.partition p] at hs
  have hcount : (∑ _i : A.centers, A.coreThreshold) =
      (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) := by
    simp [coreThreshold,div_eq_mul_inv]
  rw [hcount] at hs
  have hlt : (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hs) hlt

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteSurfacePreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite prescribed points can be prepared by one globally defined small
correction, with its C2 constant fixed before the finite set is supplied. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_spherical_preparation_correction_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (c : P → A.centers) (Q : M → Space),
        (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ Q ∧
        A.WeightedBound 1 1 ε Q ∧ A.WeightedBound 1 2 D Q ∧
        let G := radialNormalize ∘ (F+Q)
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
            (chartAt Plane (c p : M) p) v w = 0 := by
  classical
  obtain ⟨D,hD,hbudget⟩ := A.finite_surface_correction_budgets hF hunit
  refine ⟨D,hD,?_⟩
  intro P ε hε
  choose c hc using fun p : P => A.mem_some_weightCore (p : M)
  have hcn (p : P) : A.weight (c p) p ≠ 0 := A.weightCore_nonzero (c p) (hc p)
  let U (p : P) : Set M := {x | A.weight (c p) x ≠ 0}
  have hU (p : P) : IsOpen (U p) := isOpen_ne_fun (A.weight_smooth (c p)).continuous continuous_const
  have hpU (p : P) : (p : M) ∈ U p := hcn p
  let η := min 1 (ε/(D+1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hDη : D*η ≤ ε := by
    have hm := min_le_right (1 : ℝ) (ε/(D+1))
    have hh : (D+1)*η ≤ ε := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < D+1)).mp hm
    nlinarith
  obtain ⟨r,hr,hdisj⟩ := finite_point_chart_balls P
    (fun p => chartAt Plane (c p : M))
    (fun p => by simpa only [chart_source] using (A.weight_support (c p) (subset_tsupport _ (hcn p))))
    U hU hpU hη
  have ht (p : P) : closedBall (chartAt Plane (c p : M) p) (r p) ⊆
      (chartAt Plane (c p : M)).target := fun _ hx => (hr p).2.2 hx |>.1
  obtain ⟨hb1,hb2⟩ := hbudget P c r η hη hη1 hcn
    (fun p => ⟨(hr p).1,(hr p).2.1.le⟩) ht hdisj
  refine ⟨c,A.finiteSurfaceQuadratic P c r F,hcn,
    A.finiteSurfaceQuadratic_smooth P c r F,?_,hb2,?_⟩
  · exact fun i => (hb1 i).mono_const hDη
  · exact A.finiteSurfaceQuadratic_flattening P c r F hF hunit hcn
      (fun p => (hr p).1) ht hdisj

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction_oai.{u_1}
