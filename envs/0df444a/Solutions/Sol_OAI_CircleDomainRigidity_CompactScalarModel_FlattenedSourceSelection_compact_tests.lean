-- Prove2me | solution 1 for OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:44:23.521784+00:00
-- url     : https://prove2.me/submissions/0858ff1e-055c-4534-b054-14c9eebd9da6

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

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
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitelySuslinian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite bounds on disjoint continua imply local connectedness

This is the topological implication (ii) to (iii) in the generic-level
continua lemma of `047-02`, Section 1. Components of a closed ball that
meet its half-radius ball have uniformly positive diameter by boundary
bumping. There are only finitely many of them, so the component through
the center is a neighborhood of that center.
-/

open Set Filter Metric
open scoped Topology

namespace CircleDomainRigidity

/-- Finite total length gives a uniform cardinal bound when every continuum
of a fixed minimum diameter pays a positive amount of that length. The
geometric lower payment remains an explicit hypothesis. -/
theorem finite_large_continuum_bound_of_measure {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ]
    (hpayment : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C → δ ≤ μ.real C) :
    HasFiniteLargeContinuumBound X := by
  classical
  intro ε hε
  obtain ⟨δ, hδ, hpay⟩ := hpayment ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (μ.real univ / δ)
  refine ⟨N, ?_⟩
  intro S hS hdisj
  have hsum : (S.card : ℝ) * δ ≤ ∑ C ∈ S, μ.real C := by
    calc
      (S.card : ℝ) * δ = ∑ C ∈ S, δ := by simp
      _ ≤ ∑ C ∈ S, μ.real C :=
        Finset.sum_le_sum (fun C hC => hpay C (hS C hC).1 (hS C hC).2.1 (hS C hC).2.2)
  have htotal : (∑ C ∈ S, μ.real C) ≤ μ.real univ :=
    MeasureTheory.sum_measureReal_le_measureReal_univ
      (fun C hC => (hS C hC).1.isClosed.measurableSet) hdisj
  have hcard : (S.card : ℝ) ≤ μ.real univ / δ :=
    (le_div_iff₀ hδ).mpr (hsum.trans htotal)
  exact_mod_cast (hcard.trans_lt hN).le

private theorem finite_large_continuum_family {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Set X)}
    (hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ ε ≤ diam C)
    (hdisj : S.Pairwise Disjoint) : S.Finite := by
  classical
  obtain ⟨N, hN⟩ := hbound ε hε
  by_contra hinf
  obtain ⟨T, hTS, hcard⟩ := (show S.Infinite from hinf).exists_subset_card_eq (N + 1)
  have hle := hN T (fun C hC => hS C (hTS hC))
    (fun C hC D hD hne => hdisj (hTS hC) (hTS hD) hne)
  omega

private theorem closed_componentIn {X : Type*} [TopologicalSpace X]
    {F : Set X} (hF : IsClosed F) (x : X) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- A disjoint family of nondegenerate subcontinua is countable: for each
positive reciprocal diameter threshold only finitely many can occur. -/
theorem countable_disjoint_nontrivial_subcontinua {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) {S : Set (Set X)}
    (hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ C.Nontrivial)
    (hdisj : S.Pairwise Disjoint) : S.Countable := by
  let T : ℕ → Set (Set X) := fun n => {C ∈ S | 1 / ((n : ℝ) + 1) ≤ diam C}
  have hfinite (n : ℕ) : (T n).Finite :=
    finite_large_continuum_family hbound (by positivity)
      (fun C hC => ⟨(hS C hC.1).1, (hS C hC.1).2.1, hC.2⟩)
      (hdisj.mono (fun _ hC => hC.1))
  apply (Set.countable_iUnion (fun n => (hfinite n).countable)).mono
  intro C hC
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (diam_pos (hS C hC).2.2 (hS C hC).1.isBounded)
  exact mem_iUnion.mpr ⟨n, hC, hn.le⟩

/-- The nondegenerate connected components of a compact metric space are
countable under the finite-continuum bound. -/
theorem countable_nontrivial_connectedComponents {X : Type*} [MetricSpace X]
    [CompactSpace X] (hbound : HasFiniteLargeContinuumBound X) :
    {C : Set X | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable := by
  apply countable_disjoint_nontrivial_subcontinua hbound
  · rintro C ⟨⟨x, rfl⟩, hC⟩
    exact ⟨isClosed_connectedComponent.isCompact, isConnected_connectedComponent, hC⟩
  · rintro C ⟨⟨x, rfl⟩, hx⟩ D ⟨⟨y, rfl⟩, hy⟩ hne
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    exact hne ((connectedComponent_eq hxz).trans (connectedComponent_eq hyz).symm)

/-- The component of a closed ball through its center is a neighborhood
when the ambient continuum has finite bounds on large disjoint continua. -/
theorem closedBall_component_mem_nhds {X : Type*} [MetricSpace X]
    [CompactSpace X] [PreconnectedSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (x : X) {r : ℝ} (hr : 0 < r) :
    connectedComponentIn (closedBall x r) x ∈ 𝓝 x := by
  classical
  let F := closedBall x r
  let C₀ := connectedComponentIn F x
  by_cases hproper : F = univ
  · change C₀ ∈ 𝓝 x
    simp only [C₀, hproper, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]
    exact univ_mem
  have hF : IsClosed F := isClosed_closedBall
  let S : Set (Set X) := {C | ∃ y ∈ ball x (r / 2), C = connectedComponentIn F y}
  have hyF {y : X} (hy : y ∈ ball x (r / 2)) : y ∈ F := by
    change dist y x ≤ r
    have hdist : dist y x < r / 2 := hy
    linarith
  have hS : ∀ C ∈ S, IsCompact C ∧ IsConnected C ∧ r / 2 ≤ diam C := by
    rintro C ⟨y, hy, rfl⟩
    have hc : IsCompact (connectedComponentIn F y) := (closed_componentIn hF y).isCompact
    have hconn : IsConnected (connectedComponentIn F y) :=
      isConnected_connectedComponentIn_iff.mpr (hyF hy)
    obtain ⟨z, hzC, hzfront⟩ := component_meets_frontier hF hproper (hyF hy)
    have hzdist : dist z x = r := frontier_closedBall_subset_sphere hzfront
    have hyDist : dist y x < r / 2 := hy
    have hdiam := dist_le_diam_of_mem hc.isBounded hzC (mem_connectedComponentIn (hyF hy))
    have htri := dist_triangle z y x
    exact ⟨hc, hconn, by linarith⟩
  have hdisj : S.Pairwise Disjoint := by
    rintro C ⟨y, hy, rfl⟩ D ⟨z, hz, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro w hwy hwz
    exact hne ((connectedComponentIn_eq hwy).trans (connectedComponentIn_eq hwz).symm)
  have hSfinite : S.Finite := finite_large_continuum_family hbound (by positivity) hS hdisj
  let B : Set X := ⋃₀ (S \ {C₀})
  have hBclosed : IsClosed B := by
    rw [show B = ⋃₀ (S \ {C₀}) from rfl, sUnion_eq_biUnion]
    exact hSfinite.sdiff.isClosed_biUnion (fun C hC => (hS C hC.1).1.isClosed)
  have hxnotB : x ∉ B := by
    rintro ⟨C, hC, hxC⟩
    have hne : C ≠ C₀ := by simpa using hC.2
    obtain ⟨y, hy, rfl⟩ := hC.1
    exact hne (connectedComponentIn_eq hxC)
  have hVnhds : ball x (r / 2) ∩ Bᶜ ∈ 𝓝 x :=
    inter_mem (ball_mem_nhds x (by positivity)) (hBclosed.isOpen_compl.mem_nhds hxnotB)
  apply Filter.mem_of_superset hVnhds
  rintro y ⟨hy, hyB⟩
  have hCy : connectedComponentIn F y ∈ S := ⟨y, hy, rfl⟩
  have hyelem := mem_connectedComponentIn (hyF hy)
  have heq : connectedComponentIn F y = C₀ := by
    by_contra hne
    apply hyB
    exact ⟨connectedComponentIn F y, ⟨hCy, by simpa using hne⟩, hyelem⟩
  change y ∈ C₀
  rwa [← heq]

/-- A compact metric continuum with uniform finite bounds on large
pairwise disjoint subcontinua is locally connected. -/
theorem locallyConnectedSpace_of_finite_large_continuum_bound
    {X : Type*} [MetricSpace X] [CompactSpace X] [PreconnectedSpace X]
    (hbound : HasFiniteLargeContinuumBound X) : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U hU
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  exact ⟨connectedComponentIn (closedBall x r) x,
    closedBall_component_mem_nhds hbound x hr, isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset _ _).trans hsub⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HausdorffPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Length payment by crossing a ball

The generic-level-continua proof in Section 1 of `047-02` uses radial
distance on a subcontinuum crossing a ball contained in the physical
domain. Its image contains the radius interval, so one-dimensional
Hausdorff measure pays at least the ball radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

/-- Radial distance is one-Lipschitz and maps a connected set containing
two points onto an interval of length their distance. -/
theorem dist_le_hausdorffMeasure_one_of_preconnected
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {C : Set X} (hC : IsPreconnected C) {p q : X} (hp : p ∈ C) (hq : q ∈ C) :
    ENNReal.ofReal (dist q p) ≤ (μH[1] : Measure X) C := by
  have himage : IsPreconnected ((fun z => dist z p) '' C) :=
    hC.image _ (LipschitzWith.dist_left p).continuous.continuousOn
  have hinterval : Icc 0 (dist q p) ⊆ (fun z => dist z p) '' C :=
    himage.Icc_subset ⟨p, hp, dist_self p⟩ ⟨q, hq, rfl⟩
  calc
    ENNReal.ofReal (dist q p) = (μH[1] : Measure ℝ) (Icc 0 (dist q p)) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      simp only [sub_zero]
    _ ≤ (μH[1] : Measure ℝ) ((fun z => dist z p) '' C) := measure_mono hinterval
    _ ≤ (μH[1] : Measure X) C := by
      simpa using (LipschitzWith.dist_left p).hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ 1 by norm_num) C

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteLengthTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hausdorff length gives a finite-continuum bound, countability
of nontrivial components, and local connectedness. -/
open Set Function MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_length_continuum_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsFiniteMeasure (μH[1] : Measure X)] : HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_measure (μH[1] : Measure X)
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro C _hC hc hdiam
  apply hdiam.trans
  apply diam_le_of_forall_dist_le (measureReal_nonneg (μ := (μH[1] : Measure X)))
  intro x hx y hy
  have h := dist_le_hausdorffMeasure_one_of_preconnected hc.isPreconnected hy hx
  have hr := ENNReal.toReal_mono (measure_ne_top (μH[1] : Measure X) C) h
  simpa only [ENNReal.toReal_ofReal dist_nonneg, measureReal_def] using hr

 theorem finite_length_subspace_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {K : Set X} (hK : (μH[1] : Measure X) K < ∞) :
    HasFiniteLargeContinuumBound K := by
  have he : (μH[1] : Measure K) univ = (μH[1] : Measure X) K := by
    have hi : Isometry (Subtype.val : K → X) := fun _ _ => rfl
    simpa only [image_univ, Subtype.range_val] using
      (hi.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) univ).symm
  let : IsFiniteMeasure (μH[1] : Measure K) := ⟨he ▸ hK⟩
  exact finite_length_continuum_bound

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_PriorityWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable priority weights form a subprobability distribution. The
remaining mass belongs to the original horizontal coordinate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityRemainder_succ (χ : ℕ → ℝ) (n : ℕ) :
    priorityRemainder χ (n+1) = priorityRemainder χ n*(1-χ n) := by
  simp only [priorityRemainder, Finset.prod_range_succ]

 theorem priorityWeight_sum (χ : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, priorityWeight χ i = 1-priorityRemainder χ n := by
  induction n with
  | zero => simp [priorityRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, priorityRemainder_succ]
    dsimp only [priorityWeight]
    ring

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalDerivativeCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable local Lipschitz bounds that approximate the norm of the
actual differential. These are used to localize the published curve
coarea inequality without adding a weighted curve-coarea input. -/

open Set Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_local_derivative_bound
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : x ∈ D) :
    ∃ U : Set ℂ, ∃ L : ℝ≥0, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      LipschitzOnWith L f U ∧ ∀ z ∈ U, (L : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  have hdf := (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).continuousAt
    (hD.mem_nhds hx)
  have hnear : {z | ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2} ∈ 𝓝 x := by
    have hc : ContinuousAt (fun z => ‖fderiv ℝ f z - fderiv ℝ f x‖) x :=
      (hdf.sub continuousAt_const).norm
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by simpa using half_pos hε))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds hx) hnear)
  let L : ℝ≥0 := ⟨‖fderiv ℝ f x‖ + ε / 2, by positivity⟩
  refine ⟨ball x r, L, isOpen_ball, mem_ball_self hr, fun z hz => (hball hz).1, ?_, ?_⟩
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hf.differentiableOn (by norm_num) z (hball hz).1).differentiableAt
        (hD.mem_nhds (hball hz).1)) ?_ (convex_ball x r)
    intro z hz
    change ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f x‖ + ε / 2
    have hn := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f x)
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith
  · intro z hz
    change ‖fderiv ℝ f x‖ + ε / 2 ≤ ‖fderiv ℝ f z‖ + ε
    have hn := norm_sub_norm_le (fderiv ℝ f x) (fderiv ℝ f z)
    rw [norm_sub_rev] at hn
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith

theorem exists_countable_derivative_cover
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℕ → Set ℂ, ∃ L : ℕ → ℝ≥0,
      (∀ n, IsOpen (U n)) ∧ D ⊆ ⋃ n, U n ∧
      (∀ n, U n ⊆ D) ∧ (∀ n, LipschitzOnWith (L n) f (U n)) ∧
      ∀ n z, z ∈ U n → (L n : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, empty_subset _,
      fun _ => empty_subset _, fun _ => ?_, ?_⟩
    · intro z hz
      exact hz.elim
    · simp
  let : Nonempty D := hne.to_subtype
  choose U L hU hxU hUD hLip hbound using
    fun x : D => exists_local_derivative_bound hD hf hε x.property
  have hcover : D ⊆ ⋃ x : D, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨q, hq⟩ := (IsLindelof.of_coe : IsLindelof D).indexed_countable_subcover U hU hcover
  exact ⟨fun n => U (q n), fun n => L (q n), fun n => hU (q n), hq,
    fun n => hUD (q n), fun n => hLip (q n), fun n => hbound (q n)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCurveImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth scalar image is paid by the integral of the differential
against curve length. This bound is proved directly by local Lipschitz
covers and therefore needs no additional published input. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem smooth_curve_image_add_error
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {ε : ℝ} (hε : 0 < ε) :
    volume (f '' A) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨U, L, hU, hcover, _, hLip, hbound⟩ := exists_countable_derivative_cover hD hf hε
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  calc
    volume (f '' A) = volume (⋃ n, f '' E n) := by rw [← image_iUnion, hEq]
    _ ≤ ∑' n, volume (f '' E n) := measure_iUnion_le _
    _ ≤ ∑' n, (L n : ℝ≥0∞) * (μH[1] : Measure ℂ) (E n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h := ((hLip n).mono (hEU n)).hausdorffMeasure_image_le (d := 1) (by norm_num)
      simpa only [hausdorffMeasure_real, ENNReal.rpow_one] using h
    _ ≤ ∑' n, ∫⁻ z in E n, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hE n)
      intro z hz
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (norm_nonneg _) hε.le]
      exact ENNReal.ofReal_le_ofReal (hbound n z (hEU n hz))
    _ = ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
      rw [← lintegral_iUnion hE hdisj, hEq]

theorem smooth_curve_image_bound
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    volume (f '' A) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  have hbound (n : ℕ) := smooth_curve_image_add_error hD hA hAD hf
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  simp only [lintegral_add_right _ measurable_const, setLIntegral_const] at hbound
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hp := ENNReal.Tendsto.mul_const ht (Or.inr hfin.ne)
  have hall := (tendsto_const_nhds (x :=
    ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ))).add hp
  simp only [zero_mul, add_zero] at hall
  exact ge_of_tendsto hall (Eventually.of_forall hbound)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevLevelOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the smooth image estimate to a Sobolev approximation on a
finite-length level. The conclusion holds on every measurable connected
subset simultaneously; no exceptional set of arcs is introduced. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem connected_level_oscillation_of_approximation
    {K : Set ℂ} (hKfin : (μH[1] : Measure ℂ) K < ∞)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0))
    {O : Set ℂ} (hO : MeasurableSet O) (hOK : O ⊆ K) (hconn : IsPreconnected O)
    {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    ENNReal.ofReal |v x-v y| ≤ ∫⁻ z in O, g z ∂(μH[1] : Measure ℂ) := by
  have hpay (n : ℕ) : ENNReal.ofReal |u n x-u n y| ≤
      (∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))+
        ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ) := by
    have hi := dist_le_hausdorffMeasure_one_of_preconnected
      (hconn.image (u n) (hu n).continuous.continuousOn)
      (mem_image_of_mem (u n) hy) (mem_image_of_mem (u n) hx)
    rw [hausdorffMeasure_real, Real.dist_eq] at hi
    calc
      _ ≤ volume (u n '' O) := hi
      _ ≤ ∫⁻ z in O, ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ∂(μH[1] : Measure ℂ) :=
        smooth_curve_image_bound isOpen_univ hO (subset_univ _)
          ((measure_mono hOK).trans_lt hKfin) (hu n).contDiffOn
      _ ≤ ∫⁻ z in O, g z+e n z ∂(μH[1] : Measure ℂ) := by
        apply lintegral_mono_ae
        exact (hgrad n).filter_mono (ae_mono (Measure.restrict_mono hOK le_rfl))
      _ = (∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))+
          ∫⁻ z in O, e n z ∂(μH[1] : Measure ℂ) := lintegral_add_left hg _
      _ ≤ _ := add_le_add le_rfl (lintegral_mono_set (μ := (μH[1] : Measure ℂ)) (f := e n) hOK)
  have hl := ENNReal.tendsto_ofReal (((hv x (hOK hx)).sub (hv y (hOK hy))).abs)
  have hr := (tendsto_const_nhds (x := ∫⁻ z in O, g z ∂(μH[1] : Measure ℂ))).add herror
  simpa only [add_zero] using
    le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hpay)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteLevelNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A zero weighted trace on a compact locally connected finite-length
level has null scalar image. The weight and all oscillations come from
the actual smooth approximations, not from a null-image hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_level_null_image_of_approximation
    {K F : Set ℂ} (hK : IsCompact K) (hKfin : (μH[1] : Measure ℂ) K < ∞)
    [LocallyConnectedSpace K]
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hgfin : (∫⁻ z in K, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hF : MeasurableSet F)
    (hgF : (∫⁻ z in F ∩ K, g z ∂(μH[1] : Measure ℂ)) = 0)
    (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0)) :
    volume (v '' (F ∩ K)) = 0 := by
  let μ : Measure ℂ := ((μH[1] : Measure ℂ).restrict K).withDensity g
  let : IsFiniteMeasure μ := ⟨by
    change ((μH[1] : Measure ℂ).restrict K).withDensity g univ < ∞
    simpa only [withDensity_apply g MeasurableSet.univ, Measure.restrict_univ] using hgfin⟩
  have hμ (A : Set ℂ) (hA : MeasurableSet A) (hAK : A ⊆ K) :
      μ A = ∫⁻ z in A, g z ∂(μH[1] : Measure ℂ) := by
    rw [show μ = ((μH[1] : Measure ℂ).restrict K).withDensity g from rfl,
      withDensity_apply g hA, Measure.restrict_restrict hA, inter_eq_left.mpr hAK]
  have hμF : μ (F ∩ K) = 0 := by
    rw [hμ _ (hF.inter hK.isClosed.measurableSet) inter_subset_right, hgF]
  have hemb : MeasurableEmbedding (Subtype.val : K → ℂ) :=
    MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet
  let ν : Measure K := μ.comap Subtype.val
  let : IsFiniteMeasure ν := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top μ _⟩
  have hν (A : Set K) (hA : MeasurableSet A) :
      ν A = ∫⁻ z in Subtype.val '' A, g z ∂(μH[1] : Measure ℂ) := by
    rw [show ν = μ.comap Subtype.val from rfl, hemb.comap_apply]
    exact hμ _ (hemb.measurableSet_image.mpr hA) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
  have hνF : ν (Subtype.val ⁻¹' F) = 0 := by
    change μ.comap Subtype.val (Subtype.val ⁻¹' F) = 0
    rw [hemb.comap_apply, Subtype.image_preimage_coe, inter_comm, hμF]
  have hn := null_image_of_connected_open_oscillation (μ := ν) hνF
    (fun z : K => v z.val) (by norm_num : (0 : ℝ) ≤ 1) (by
      intro A hA hc x hx y hy
      have hAK : Subtype.val '' A ⊆ K := by rintro _ ⟨z, _, rfl⟩; exact z.property
      have hp := connected_level_oscillation_of_approximation hKfin u hu hv g hg e hgrad herror
        (hemb.measurableSet_image.mpr hA.measurableSet) hAK
        (hc.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn)
        (mem_image_of_mem Subtype.val hx.2) (mem_image_of_mem Subtype.val hy.2)
      rw [← hν A hA.measurableSet] at hp
      have hr := ENNReal.toReal_mono (measure_ne_top ν A) hp
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def, one_mul] using hr)
  have himage : (fun z : K => v z.val) '' (Subtype.val ⁻¹' F) = v '' (F ∩ K) := by
    ext t
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, ⟨hz, z.property⟩, rfl⟩
    · rintro ⟨z, ⟨hzF, hzK⟩, rfl⟩
      exact ⟨⟨z, hzK⟩, hzF, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteLevelComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a finite-length compact level, the countable nontrivial components
carry every point at which a level continuum has been constructed. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem finite_level_components_null_image
    {K F : Set ℂ} (hK : IsCompact K) (hKfin : (μH[1] : Measure ℂ) K < ∞)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {v : ℂ → ℝ}
    (hv : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hgfin : (∫⁻ z in K, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hF : MeasurableSet F)
    (hgF : (∫⁻ z in F ∩ K, g z ∂(μH[1] : Measure ℂ)) = 0)
    (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n, ∀ᵐ z ∂(μH[1] : Measure ℂ).restrict K,
      ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (herror : Tendsto (fun n => ∫⁻ z in K, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0))
    (hcover : ∀ z (_hzF : z ∈ F) (hzK : z ∈ K),
      (connectedComponent (⟨z, hzK⟩ : K)).Nontrivial) :
    volume (v '' (F ∩ K)) = 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (Set K) := {C | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}
  have hS : S.Countable := countable_nontrivial_connectedComponents (finite_length_subspace_bound hKfin)
  have hnull (C : Set K) (hC : C ∈ S) : volume (v '' (F ∩ (Subtype.val '' C))) = 0 := by
    obtain ⟨⟨x, rfl⟩, _⟩ := hC
    let D : Set ℂ := Subtype.val '' connectedComponent x
    have hDc : IsCompact D := isClosed_connectedComponent.isCompact.image continuous_subtype_val
    have hDconn : IsConnected D := isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hDK : D ⊆ K := by rintro _ ⟨y, _, rfl⟩; exact y.property
    have hDfin : (μH[1] : Measure ℂ) D < ∞ := (measure_mono hDK).trans_lt hKfin
    let : CompactSpace D := isCompact_iff_compactSpace.mp hDc
    let : PreconnectedSpace D := Subtype.preconnectedSpace hDconn.isPreconnected
    let : LocallyConnectedSpace D := locallyConnectedSpace_of_finite_large_continuum_bound
      (finite_length_subspace_bound hDfin)
    apply finite_level_null_image_of_approximation hDc hDfin u hu
      (fun z hz => hv z (hDK hz)) g hg
      ((lintegral_mono_set hDK).trans_lt hgfin) hF ?_ e ?_ ?_
    · apply le_antisymm _ bot_le
      exact (lintegral_mono_set (μ := (μH[1] : Measure ℂ)) (f := g)
        (inter_subset_inter_right F hDK)).trans_eq hgF
    · intro n
      exact (hgrad n).filter_mono (ae_mono (Measure.restrict_mono hDK le_rfl))
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
        (fun _ => bot_le) (fun n => lintegral_mono_set hDK)
  have himage : v '' (F ∩ K) ⊆ ⋃ C ∈ S, v '' (F ∩ (Subtype.val '' C)) := by
    rintro _ ⟨z, hz, rfl⟩
    let x : K := ⟨z, hz.2⟩
    refine mem_iUnion.mpr ⟨connectedComponent x, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact ⟨⟨x, rfl⟩, hcover z hz.1 hz.2⟩
    · exact ⟨z, ⟨hz.1, x, mem_connectedComponent, rfl⟩, rfl⟩
  exact measure_mono_null himage ((measure_biUnion_null_iff hS).mpr hnull)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first-exit cuts for the collar-splicing construction. Every
retained initial fragment lies in the corresponding closed collar disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem firstExitTime_le (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : γ t ∉ V) : firstExitTime γ V ≤ t :=
  sInf_le ht

theorem mem_before_firstExit (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : t < firstExitTime γ V) : γ t ∈ V := by
  by_contra hn
  exact ht.not_ge (firstExitTime_le γ V hn)

theorem firstExit_notMem (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∉ V := by
  exact (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem ⟨⊤, hend⟩

theorem firstExit_pos (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : ⊥ < firstExitTime γ V := by
  apply bot_lt_iff_ne_bot.mpr
  intro he
  exact firstExit_notMem γ hV hend (he ▸ hstart)

theorem firstExit_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∈ frontier V := by
  have hpos := firstExit_pos γ hV hstart hend
  have hcl : firstExitTime γ V ∈ closure (Iio (firstExitTime γ V)) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : firstExitTime γ V ≤ firstExitTime γ V)
  have hmap : MapsTo γ (Iio (firstExitTime γ V)) V := fun _ ht => mem_before_firstExit γ V ht
  rw [frontier, hV.interior_eq]
  exact ⟨hmap.closure γ.continuous hcl, firstExit_notMem γ hV hend⟩

theorem firstExit_initial_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) :
    MapsTo γ (Iic (firstExitTime γ V)) (closure V) := by
  intro t ht
  change t ≤ firstExitTime γ V at ht
  rcases ht.eq_or_lt with rfl | hlt
  · exact frontier_subset_closure (firstExit_frontier γ hV hstart hend)
  · exact subset_closure (mem_before_firstExit γ V hlt)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HomeomorphicLevelContinuum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial pieces of actual horizontal inverse lines provide compact
level continua from the centre to the boundary of any closed disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_level_continuum (φ : ℂ ≃ₜ ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ K : Set ℂ, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧
      K ⊆ closedBall x r ∧ (∀ y ∈ K, (φ y).im = (φ x).im) ∧
      (K ∩ sphere x r).Nonempty := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x r).image φ.continuous).isBounded.subset_ball 0
  let q : ℂ := ⟨max B 0+1, (φ x).im⟩
  have hq : φ.symm q ∉ closedBall x r := by
    intro h
    have hb : ‖q‖ < B := by
      have hh := hB (mem_image_of_mem φ h)
      simpa only [φ.apply_symm_apply, mem_ball, dist_zero_right] using hh
    have hle : max B 0+1 ≤ ‖q‖ := Complex.re_le_norm q
    linarith [le_max_left B 0]
  let γ : C(PathTime, ℂ) := ⟨fun t => φ.symm (φ x+(t : ℝ) • (q-φ x)), by fun_prop⟩
  have hstart : γ ⊥ = x := by simp [γ]
  have hstop : γ ⊤ ∉ ball x r := by
    have he : γ ⊤ = φ.symm q := by simp [γ]
    rw [he]
    exact fun h => hq (ball_subset_closedBall h)
  let τ := firstExitTime γ (ball x r)
  have hstartB : γ ⊥ ∈ ball x r := hstart ▸ mem_ball_self hr
  have hboundary : γ τ ∈ sphere x r := by
    have h := firstExit_frontier γ isOpen_ball hstartB hstop
    simpa only [frontier_ball x hr.ne'] using h
  let K := γ '' Iic τ
  have hc : IsConnected (Iic τ : Set PathTime) :=
    ⟨⟨⊥, mem_Iic.mpr bot_le⟩, isPreconnected_Iic⟩
  refine ⟨K, isClosed_Iic.isCompact.image γ.continuous, hc.image _ γ.continuous.continuousOn,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨⊥, mem_Iic.mpr bot_le, hstart⟩
  · rintro y ⟨t, ht, rfl⟩
    have hh := firstExit_initial_segment γ isOpen_ball hstartB hstop ht
    simpa only [closure_ball x hr.ne'] using hh
  · rintro y ⟨t, ht, rfl⟩
    simp [γ, q, Complex.add_im, Complex.sub_im]
  · exact ⟨γ τ, ⟨τ, mem_Iic.mpr le_rfl, rfl⟩, hboundary⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NestedCompactContinua
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact intersection step for limiting level continua. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

 theorem preconnected_iInter_compact_antitone
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (hc : ∀ n, IsPreconnected (K n)) (hm : Antitone K) :
    IsPreconnected (⋂ n, K n) := by
  have hclosed : IsClosed (⋂ n, K n) := isClosed_iInter (fun n => (hK n).isClosed)
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hclosed]
  intro a b ha hb hcover hab
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := normal_separation ha hb hab
  have hdis : Disjoint (K 0 ∩ (U ∪ V)ᶜ) (⋂ n, K n) := by
    apply Set.disjoint_left.mpr
    intro p hp hpK
    exact hp.2 ((hcover hpK).elim (fun h => Or.inl (haU h)) (fun h => Or.inr (hbV h)))
  have hcompact := (hK 0).inter_right (hU.union hV).isClosed_compl
  obtain ⟨n, hn⟩ := hcompact.elim_directed_family_closed K
    (fun n => (hK n).isClosed) (Set.disjoint_iff_inter_eq_empty.mp hdis) hm.directed_ge
  have hKn : K n ⊆ U ∪ V := by
    intro p hp
    by_contra hout
    exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hn) ⟨hm (Nat.zero_le n) hp, hout⟩ hp
  rcases (hc n).subset_or_subset hU hV hUV hKn with hleft | hright
  · left
    intro p hp
    rcases hcover hp with hpA | hpB
    · exact hpA
    · exact False.elim (Set.disjoint_left.mp hUV (hleft (mem_iInter.mp hp n)) (hbV hpB))
  · right
    intro p hp
    rcases hcover hp with hpA | hpB
    · exact False.elim (Set.disjoint_left.mp hUV (haU hpA) (hright (mem_iInter.mp hp n)))
    · exact hpB

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LimitLevelContinuum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact level continuum obtained from connected approximating
sets with a common point. Tail closures retain contact with a closed
boundary set; no choice of a Hausdorff subsequence is needed. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_limit_level_continuum
    {X : Type*} [MetricSpace X] {S E : Set X} (hS : IsCompact S) (hE : IsClosed E)
    (f : ℕ → X → ℝ) {v : X → ℝ} (hv : Continuous v)
    (hlim : TendstoUniformlyOn f v atTop S)
    (K : ℕ → Set X) (hc : ∀ n, IsConnected (K n)) (hKS : ∀ n, K n ⊆ S)
    {x : X} (hx : ∀ n, x ∈ K n)
    (hlevel : ∀ n y, y ∈ K n → f n y = f n x)
    (hmeet : ∀ n, (K n ∩ E).Nonempty) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ x ∈ C ∧ C ⊆ S ∧
      (∀ y ∈ C, v y = v x) ∧ (C ∩ E).Nonempty := by
  let T (n : ℕ) : Set X := closure (⋃ m : {m : ℕ // n ≤ m}, K m.val)
  have hsub (n : ℕ) : T n ⊆ S := by
    apply closure_minimal _ hS.isClosed
    exact iUnion_subset (fun m => hKS m.val)
  have hxT (n : ℕ) : x ∈ T n :=
    subset_closure (mem_iUnion_of_mem ⟨n, le_rfl⟩ (hx n))
  have hm : Antitone T := by
    intro n m hnm
    apply closure_mono
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    exact mem_iUnion_of_mem ⟨k.val, hnm.trans k.property⟩ hk
  have hTc (n : ℕ) : IsCompact (T n) :=
    hS.of_isClosed_subset isClosed_closure (hsub n)
  have hTp (n : ℕ) : IsPreconnected (T n) := by
    apply IsPreconnected.closure
    apply isPreconnected_iUnion
    · exact ⟨x, mem_iInter.mpr (fun _ => hx _)⟩
    · exact fun m => (hc m.val).isPreconnected
  let C := ⋂ n, T n
  have hxC : x ∈ C := mem_iInter.mpr hxT
  have hCS : C ⊆ S := (iInter_subset T 0).trans (hsub 0)
  have hCc : IsCompact C :=
    hS.of_isClosed_subset (isClosed_iInter (fun _ => isClosed_closure)) hCS
  have hconn : IsConnected C :=
    ⟨⟨x, hxC⟩, preconnected_iInter_compact_antitone T hTc hTp hm⟩
  have hCE : (C ∩ E).Nonempty := by
    have hmE : Antitone (fun n => T n ∩ E) := fun n m h => inter_subset_inter_left _ (hm h)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun n => T n ∩ E) hmE.directed_ge
      (fun n => by
        obtain ⟨y, hyK, hyE⟩ := hmeet n
        exact ⟨y, subset_closure (mem_iUnion_of_mem ⟨n, le_rfl⟩ hyK), hyE⟩)
      (fun n => (hTc n).inter_right hE) (fun _ => isClosed_closure.inter hE)
    exact ⟨y, mem_iInter.mpr (fun n => (mem_iInter.mp hy n).1), (mem_iInter.mp hy 0).2⟩
  refine ⟨C, hCc, hconn, hxC, hCS, ?_, hCE⟩
  intro y hy
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hlim) (ε/2) (half_pos hε))
  have hband : T N ⊆ {z | dist (v z) (v x) ≤ ε} := by
    apply closure_minimal _ (isClosed_le (hv.dist continuous_const) continuous_const)
    intro z hz
    obtain ⟨m, hm⟩ := mem_iUnion.mp hz
    change dist (v z) (v x) ≤ ε
    have ha := hN m.val m.property z (hKS m.val hm)
    have hb := hN m.val m.property x (hKS m.val (hx m.val))
    rw [hlevel m.val z hm] at ha
    have ht := dist_triangle (v z) (f m.val z) (v x)
    rw [hlevel m.val z hm, dist_comm (f m.val x)] at ht
    linarith
  exact hband (mem_iInter.mp hy N)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HeightLevelContinuum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every point of an actual limiting homeomorphic height belongs to
a nondegenerate compact continuum of its level in each centred disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem height_level_continuum
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Set ℂ, IsCompact C ∧ IsConnected C ∧ C.Nontrivial ∧ x ∈ C ∧
      C ⊆ closedBall x r ∧ (∀ y ∈ C, v y = v x) ∧
      (C ∩ sphere x r).Nonempty := by
  choose K hK hc hx hsub hlevel hmeet using
    (fun n => homeomorphic_level_continuum (φ n) x hr)
  obtain ⟨C, hCc, hconn, hxC, hCS, hCv, hCE⟩ :=
    exists_limit_level_continuum (isCompact_closedBall x r) isClosed_sphere
      (fun n z => (φ n z).im) hv
      ((tendstoLocallyUniformly_iff_forall_isCompact.mp hlim) _ (isCompact_closedBall x r))
      K hc hsub hx hlevel hmeet
  obtain ⟨y, hyC, hy⟩ := hCE
  have hne : x ≠ y := by
    intro he
    rw [← he, mem_sphere, dist_self] at hy
    exact hr.ne' hy.symm
  exact ⟨C, hCc, hconn, ⟨x, hxC, y, hyC, hne⟩, hxC, hCS, hCv, y, hyC, hy⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LevelComponentNontrivial
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A pointwise level continuum makes the component of the full compact
level section nontrivial. This includes every interior point. -/
open Set Function Filter MeasureTheory Metric Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nontrivial_component_of_continuum
    {K C : Set ℂ} {x : ℂ} (hx : x ∈ K)
    (hc : IsConnected C) (hnt : C.Nontrivial) (hxC : x ∈ C) (hCK : C ⊆ K) :
    (connectedComponent (⟨x, hx⟩ : K)).Nontrivial := by
  let A : Set K := Subtype.val ⁻¹' C
  have him : Subtype.val '' A = C := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
  have hA : IsPreconnected A := IsInducing.subtypeVal.isPreconnected_image.mp (him ▸ hc.isPreconnected)
  have hsub : A ⊆ connectedComponent (⟨x, hx⟩ : K) := hA.subset_connectedComponent hxC
  apply Set.Nontrivial.mono ?_ hsub
  obtain ⟨a, ha, b, hb, hab⟩ := hnt
  exact ⟨⟨a, hCK ha⟩, ha, ⟨b, hCK hb⟩, hb, fun he => hab (congrArg Subtype.val he)⟩

 theorem height_level_component_nontrivial
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {Q : Set ℂ} {x : ℂ} (hxQ : x ∈ interior Q) :
    (connectedComponent (⟨x, ⟨interior_subset hxQ, rfl⟩⟩ :
      {z : ℂ // z ∈ Q ∧ v z = v x})).Nontrivial := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hxQ)
  obtain ⟨C, _, hc, hnt, hx, hCb, hlev, _⟩ := height_level_continuum φ hv hlim x hr
  apply nontrivial_component_of_continuum _ hc hnt hx
  intro y hy
  exact ⟨hsub (hCb hy), hlev y hy⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FullLevelNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual level continua cover every interior trace point by the
countable nontrivial components of the full compact level section. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem full_level_null_image_of_approximation
    (φ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (φ n z).im) v atTop)
    {Q F : Set ℂ} (hQ : IsCompact Q) (hF : MeasurableSet F) (hFQ : F ⊆ interior Q)
    (u : ℕ → ℂ → ℝ) (hu : ∀ n, ContDiff ℝ 1 (u n)) {U : ℂ → ℝ}
    (hU : ∀ z ∈ Q, Tendsto (fun n => u n z) atTop (𝓝 (U z)))
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (e : ℕ → ℂ → ℝ≥0∞)
    (hgrad : ∀ n z, ENNReal.ofReal ‖fderiv ℝ (u n) z‖ ≤ g z+e n z)
    (hfinite : ∀ᵐ t ∂volume, (μH[1] : Measure ℂ) (Q ∩ {z | v z = t}) < ∞)
    (hgfinite : ∀ᵐ t ∂volume,
      (∫⁻ z in Q ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞)
    (hgzero : ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) = 0)
    (herror : ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in Q ∩ {z | v z = t}, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0)) :
    ∀ᵐ t ∂volume, volume (U '' (F ∩ {z | v z = t})) = 0 := by
  have hFQ' : F ⊆ Q := hFQ.trans interior_subset
  filter_upwards [hfinite, hgfinite, hgzero, herror] with t ht hgt hgzt het
  have heq : F ∩ (Q ∩ {z | v z = t}) = F ∩ {z | v z = t} := by
    rw [← inter_assoc, inter_eq_left.mpr hFQ']
  have hK : IsCompact (Q ∩ {z | v z = t}) := hQ.inter_right (isClosed_eq hv continuous_const)
  have hh := finite_level_components_null_image hK ht u hu
    (fun z hz => hU z hz.1) g hg hgt hF (by rwa [heq]) e
    (fun n => Eventually.of_forall (hgrad n)) het (by
      intro z hzF hzK
      have hzt : v z = t := hzK.2
      subst t
      exact height_level_component_nontrivial φ hv hlim (hFQ hzF))
  rwa [heq] at hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaSummableErrors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One null exceptional set controls all errors in a summable smooth
approximation on every full pointwise level. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_summable_errors
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    (e : ℕ → EuclideanPlane → ℝ≥0∞) (he : ∀ n, Measurable (e n))
    (hsum : (∑' n, ∫⁻ p in E, e n p * ENNReal.ofReal ‖V p‖) < ∞) :
    ∀ᵐ t ∂volume,
      (∑' n, sobolevLevelIntegral E v (e n) t) < ∞ ∧
      Tendsto (fun n => sobolevLevelIntegral E v (e n) t) atTop (𝓝 0) := by
  have hm (n : ℕ) := (hcoarea v hv V hw hLp E hE hb (e n) (he n)).1
  have hi : (∫⁻ t, ∑' n, sobolevLevelIntegral E v (e n) t) < ∞ := by
    rw [lintegral_tsum hm]
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext n
    exact (hcoarea v hv V hw hLp E hE hb (e n) (he n)).2
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hi.ne] with t ht
  exact ⟨ht, ENNReal.tendsto_atTop_zero_of_tsum_ne_top ht.ne⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2WeightedErrorSeries
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable L² errors give summable weighted integrals by the fixed
L² gradient in scalar coarea. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lintegral_norm_mul_le_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫⁻ p, ENNReal.ofReal ‖f p‖*ENNReal.ofReal ‖g p‖ ∂μ) ≤
      ENNReal.ofReal ((eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal) := by
  simp_rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  have hi := ofReal_integral_eq_lintegral_ofReal (hf.norm.integrable_mul hg.norm)
    (Eventually.of_forall (fun p => mul_nonneg (norm_nonneg (f p)) (norm_nonneg (g p))))
  simp only [Pi.mul_apply] at hi
  rw [← hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ p, ‖f p‖*‖g p‖ ∂μ) ≤ |∫ p, ‖f p‖*‖g p‖ ∂μ| := le_abs_self _
    _ ≤ _ := by
      simpa only [eLpNorm_norm _,
        eLpNorm_norm _] using
        abs_integral_mul_le_eLpNorm_two hf.norm hg.norm

 theorem weighted_L2_errors_summable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : ℕ → X → ℝ) {g : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hs : Summable (fun n => (eLpNorm (f n) 2 μ).toReal)) :
    (∑' n, ∫⁻ p, ENNReal.ofReal ‖f n p‖*ENNReal.ofReal ‖g p‖ ∂μ) < ∞ := by
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => lintegral_norm_mul_le_L2 (hf n) hg))
    (hs.mul_right (eLpNorm g 2 μ).toReal).tsum_ofReal_lt_top

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevCoareaFiniteLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coarea integral is finite on each bounded measurable set. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_gradient_integrableOn_bounded
    {V : EuclideanPlane → EuclideanPlane}
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hb : IsBounded E) : IntegrableOn (fun p => ‖V p‖) E := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact hV.norm.integrable (by norm_num)

 theorem sobolev_coarea_ae_finite_levels
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E) :
    ∀ᵐ t ∂volume, (μH[1] : Measure EuclideanPlane) (E ∩ {p | v p = t}) < ∞ := by
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb (fun _ => 1) measurable_const
  simp only [one_mul] at he
  have hi : (∫⁻ p in E, ENNReal.ofReal ‖V p‖) < ∞ := by
    simpa only [hasFiniteIntegral_iff_enorm, enorm_norm, ofReal_norm] using
      (local_gradient_integrableOn_bounded hLp hb).hasFiniteIntegral
  have ha := ae_lt_top' hm (he.trans_lt hi).ne
  simpa only [sobolevLevelIntegral, lintegral_one, Measure.restrict_apply_univ] using ha

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaL2Errors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable strong Sobolev errors vanish on almost every full level,
with the exceptional values independent of any later arc or component. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_L2_errors
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Measurable (f n))
    (hL : ∀ n, MemLp (f n) 2 (volume.restrict E))
    (hs : Summable (fun n => (eLpNorm (f n) 2 (volume.restrict E)).toReal)) :
    ∀ᵐ t ∂volume,
      Tendsto (fun n => sobolevLevelIntegral E v (fun p => ENNReal.ofReal ‖f n p‖) t)
        atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  have hsum := weighted_L2_errors_summable f hL hV.norm hs
  have hh := coarea_summable_errors hcoarea hv hw hLp hE hb
    (fun n p => ENNReal.ofReal ‖f n p‖)
    (fun n => ENNReal.measurable_ofReal.comp (hf n).norm) (by simpa only [norm_norm] using hsum)
  exact hh.mono (fun _ h => h.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaL2Weight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A locally square-integrable weight is integrable on almost every
bounded scalar Sobolev level. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem coarea_L2_weight_finite
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : EuclideanPlane → ℝ} (hq : Measurable q) (hL : MemLp q 2 (volume.restrict E)) :
    ∀ᵐ t ∂volume, sobolevLevelIntegral E v (fun p => ENNReal.ofReal ‖q p‖) t < ∞ := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  have hV : MemLp V 2 (volume.restrict E) :=
    (memLp_piLp_iff.mpr (hLp R)).mono_measure (Measure.restrict_mono hR le_rfl)
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb
    (fun p => ENNReal.ofReal ‖q p‖) (ENNReal.measurable_ofReal.comp hq.norm)
  have hbound := lintegral_norm_mul_le_L2 hL hV.norm
  simp only [norm_norm] at hbound
  apply ae_lt_top' hm
  rw [he]
  exact (hbound.trans_lt ENNReal.ofReal_lt_top).ne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalRoundIntegrals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ComplexHausdorffTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical coordinate chart is an isometry, including for the
Hausdorff-length measures on the full pointwise coarea levels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complexPlaneCoordinates_hausdorff_preserving :
    MeasurePreserving complexPlaneCoordinates (μH[1] : Measure EuclideanPlane) (μH[1] : Measure ℂ) :=
  complexPlaneIsometry.measurePreserving_hausdorffMeasure 1

 theorem complex_hausdorff_set_integral (E : Set ℂ) (q : ℂ → ℝ≥0∞) :
    (∫⁻ p in complexPlaneCoordinates ⁻¹' E, q (complexPlaneCoordinates p)
      ∂(μH[1] : Measure EuclideanPlane)) = ∫⁻ z in E, q z ∂(μH[1] : Measure ℂ) :=
  complexPlaneCoordinates_hausdorff_preserving.setLIntegral_comp_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding q E

 theorem complex_sobolev_level_integral (E : Set ℂ) (v : ℂ → ℝ) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
      (v ∘ complexPlaneCoordinates) (q ∘ complexPlaneCoordinates) t =
      ∫⁻ z in E ∩ {z | v z = t}, q z ∂(μH[1] : Measure ℂ) := by
  exact complex_hausdorff_set_integral (E ∩ {z | v z = t}) q

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCoareaControls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar coarea estimates transported to full complex-plane levels. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physical_complex_level_integral (E : Set ℂ) (v : ℂ → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) :
    sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E) (v ∘ complexPlaneCoordinates) q t =
      ∫⁻ z in E ∩ {z | v z = t}, q (complexPlaneCoordinates.symm z) ∂(μH[1] : Measure ℂ) := by
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    complex_sobolev_level_integral E v (q ∘ complexPlaneCoordinates.symm) t

 theorem complex_coarea_finite_levels (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E) :
    ∀ᵐ t ∂volume, (μH[1] : Measure ℂ) (E ∩ {z | v z = t}) < ∞ := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := sobolev_coarea_ae_finite_levels hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded
  filter_upwards [ht] with t ht
  have he := physical_complex_level_integral E v (fun _ => 1) t
  simp only [sobolevLevelIntegral, lintegral_one, Measure.restrict_apply_univ] at he
  rwa [← he]

 theorem complex_coarea_L2_weight_finite (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E)
    {q : EuclideanPlane → ℝ} (hq : Measurable q)
    (hL : MemLp q 2 (volume.restrict (complexPlaneCoordinates ⁻¹' E))) :
    ∀ᵐ t ∂volume,
      (∫⁻ z in E ∩ {z | v z = t}, ENNReal.ofReal ‖q (complexPlaneCoordinates.symm z)‖
        ∂(μH[1] : Measure ℂ)) < ∞ := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := coarea_L2_weight_finite hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded hq hL
  change ∀ᵐ t ∂volume, sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
    (v ∘ complexPlaneCoordinates) (fun p => ENNReal.ofReal ‖q p‖) t < ∞ at ht
  simpa only [physical_complex_level_integral] using ht

 theorem complex_coarea_L2_errors (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E)
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Measurable (f n))
    (hL : ∀ n, MemLp (f n) 2 (volume.restrict (complexPlaneCoordinates ⁻¹' E)))
    (hs : Summable (fun n => (eLpNorm (f n) 2
      (volume.restrict (complexPlaneCoordinates ⁻¹' E))).toReal)) :
    ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in E ∩ {z | v z = t}, ENNReal.ofReal ‖f n (complexPlaneCoordinates.symm z)‖
        ∂(μH[1] : Measure ℂ)) atTop (𝓝 0) := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := coarea_L2_errors hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded f hf hL hs
  change ∀ᵐ t ∂volume, Tendsto (fun n => sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
    (v ∘ complexPlaneCoordinates) (fun p => ENNReal.ofReal ‖f n p‖) t) atTop (𝓝 0) at ht
  simpa only [physical_complex_level_integral] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaZeroProduct
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarea transfers a zero weighted Jacobian to zero length on almost
every full level; either vanishing gradient may supply the product zero. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_level_integral_zero_of_product_zero
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q)
    (hz : ∀ᵐ p ∂volume.restrict E, q p*ENNReal.ofReal ‖V p‖ = 0) :
    ∀ᵐ t ∂volume, sobolevLevelIntegral E v q t = 0 := by
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb q hq
  have hzero : (∫⁻ p in E, q p*ENNReal.ofReal ‖V p‖) = 0 :=
    lintegral_eq_zero_of_ae_eq_zero hz
  rw [hzero] at he
  exact (lintegral_eq_zero_iff' hm).mp he

 theorem complex_coarea_zero_product (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {F : Set ℂ} (hF : IsCompact F)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      q p*ENNReal.ofReal ‖V p‖ = 0) :
    ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, q (complexPlaneCoordinates.symm z) ∂(μH[1] : Measure ℂ)) = 0 := by
  have hFc : IsCompact (complexPlaneCoordinates ⁻¹' F) :=
    complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  have ht := sobolev_level_integral_zero_of_product_zero hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hFc.measurableSet hFc.isBounded hq hz
  simpa only [physical_complex_level_integral] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexGradientError
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth approximation is controlled by the two scalar weak-gradient
components and their actual coordinate errors. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexCovector_norm_le_abs (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1|+|L Complex.I| := by
  have h := complexCovector_norm_sq L
  nlinarith [norm_nonneg L, abs_nonneg (L 1), abs_nonneg (L Complex.I),
    sq_abs (L 1), sq_abs (L Complex.I), mul_nonneg (abs_nonneg (L 1)) (abs_nonneg (L Complex.I))]

 theorem complex_scalar_gradient_error {u : EuclideanPlane → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p : EuclideanPlane) (a b : ℝ) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates p)‖ ≤
      |a|+|b| + (|fderiv ℝ u p (EuclideanSpace.single 0 1)-a|+
        |fderiv ℝ u p (EuclideanSpace.single 1 1)-b|) := by
  have h := complexCovector_norm_le_abs
    (fderiv ℝ (u ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates p))
  dsimp only [Function.comp_def] at h
  rw [← complexPlaneCoordinates_zero, physical_complex_partial hu,
    ← complexPlaneCoordinates_one, physical_complex_partial hu] at h
  have h0 : |fderiv ℝ u p (EuclideanSpace.single 0 1)| ≤
      |a|+|fderiv ℝ u p (EuclideanSpace.single 0 1)-a| := by
    calc
      _ = |a+(fderiv ℝ u p (EuclideanSpace.single 0 1)-a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have h1 : |fderiv ℝ u p (EuclideanSpace.single 1 1)| ≤
      |b|+|fderiv ℝ u p (EuclideanSpace.single 1 1)-b| := by
    calc
      _ = |b+(fderiv ℝ u p (EuclideanSpace.single 1 1)-b)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  dsimp only [Function.comp_def]
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SummableErrorExtraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A vanishing nonnegative error has an explicit summable extraction.
The selected indices still tend to infinity. -/
open Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_summable_error_extraction {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) (ht : Tendsto b atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, Tendsto s atTop atTop ∧ Summable (fun n => b (s n)) := by
  have hex (j : ℕ) : ∃ n, j ≤ n ∧ b n ≤ (1/2 : ℝ)^j := by
    have hs := ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (1/2 : ℝ)^j))
    obtain ⟨n, hn, hn'⟩ := ((eventually_ge_atTop j).and hs).exists
    exact ⟨n, hn, hn'.le⟩
  choose s hs he using hex
  refine ⟨s, tendsto_atTop_mono hs tendsto_id, ?_⟩
  exact Summable.of_nonneg_of_le (fun n => hb (s n)) he
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local positive smoothing with errors relative to the original weak
gradient. Compact cutoffs are removed on a neighborhood of the core. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem tendsto_eLpNorm_restrict_zero
    {f : ℕ → EuclideanPlane → ℝ} {V : Set EuclideanPlane}
    (hf : Tendsto (fun n => eLpNorm (f n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun _ => bot_le) (fun n => eLpNorm_mono_measure (f n) Measure.restrict_le_self)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_UniformSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous uniform and gradient approximation on a compact planar
set. The approximants are the actual positive convolutions of a cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_uniform_sobolev_approximation
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hc : Continuous u) :
    ∃ φ : ℕ → EuclideanPlane → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      TendstoUniformlyOn φ u atTop K ∧
      (∀ i : Fin 2, Tendsto (fun n => eLpNorm (fun p =>
        fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
        2 (volume.restrict K)) atTop (𝓝 0)) := by
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun p => η p*u p
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwL : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have heq : EqOn w u V := fun p hp => by dsimp only [w]; rw [hone p hp, one_mul]
  refine ⟨planarMollification w, fun n =>
    ⟨planarMollification_smooth (hwL.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n⟩, ?_, ?_⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have ht := planarMollification_uniform_on_compact hwL.aestronglyMeasurable hK
      hV hKV (hη.continuous.mul hc).continuousOn hε
    filter_upwards [ht] with n hn p hp
    rw [Real.dist_eq, abs_sub_comm, ← heq (hKV hp)]
    exact hn p hp
  · intro i
    have hg := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := K)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    have hgK := hg.filter_mono
      (ae_mono (Measure.restrict_mono hKV le_rfl))
    filter_upwards [hgK] with p hp
    rw [hp]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SummableSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform smooth approximation with summable errors in both actual
weak partial derivatives on a compact set. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_summable_sobolev_approximation
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hc : Continuous u) :
    ∃ φ : ℕ → EuclideanPlane → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      TendstoUniformlyOn φ u atTop K ∧
      (∀ i : Fin 2, Summable (fun n => (eLpNorm (fun p =>
        fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
        2 (volume.restrict K)).toReal)) := by
  obtain ⟨φ, hφ, hU, hG⟩ := exists_uniform_sobolev_approximation hΩ hK hKΩ hu hc
  let a (i : Fin 2) (n : ℕ) := (eLpNorm (fun p =>
    fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-hu.weakGrad p i)
    2 (volume.restrict K)).toReal
  have ht (i : Fin 2) : Tendsto (a i) atTop (𝓝 0) := by
    simpa only [a, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp)).comp (hG i)
  obtain ⟨s, hs, hsum⟩ := exists_summable_error_extraction
    (b := fun n => a 0 n+a 1 n) (fun n => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (by simpa using (ht 0).add (ht 1))
  refine ⟨φ ∘ s, fun n => hφ (s n), ?_, ?_⟩
  · intro U hU'
    exact hs.eventually (hU U hU')
  · intro i
    change Summable (fun n => a i (s n))
    apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ hsum
    intro n
    fin_cases i
    · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    · exact le_add_of_nonneg_left ENNReal.toReal_nonneg

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SobolevHeightLevelNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null scalar images of almost every full height level, constructed
from the actual smooth approximation and the scalar coarea identity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_coordinate_level_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0 ∨ W.weakGrad p = 0) :
    ∀ᵐ t ∂volume, volume ((U ∘ complexPlaneCoordinates.symm) '' (F ∩ {z | v z = t})) = 0 := by
  let K := complexPlaneCoordinates ⁻¹' Q
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hQ
  let B := borelSobolevWitness W
  let G : Fin 2 → Lp ℝ 2 (volume : Measure EuclideanPlane) := scalarGradientRepresentative W
  obtain ⟨φ, hφ, hφU, hφG⟩ := exists_summable_sobolev_approximation isOpen_univ hK
    (subset_univ _) B hU
  let f : Fin 2 → ℕ → EuclideanPlane → ℝ := fun i n p =>
    fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-G i p
  have hf (i : Fin 2) (n : ℕ) : Measurable (f i n) :=
    (((hφ n).1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.sub
      (Lp.stronglyMeasurable (G i)).measurable
  have hfL (i : Fin 2) (n : ℕ) : MemLp (f i n) 2 (volume.restrict K) := by
    have hD : MemLp (fun p => fderiv ℝ (φ n) p (EuclideanSpace.single i 1)) 2 volume := (((hφ n).1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hφ n).2.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    exact (hD.restrict K).sub ((Lp.memLp (G i)).restrict K)
  have hfs (i : Fin 2) : Summable (fun n => (eLpNorm (f i n) 2 (volume.restrict K)).toReal) :=
    hφG i
  let q : EuclideanPlane → ℝ := fun p => |G 0 p|+|G 1 p|
  have hq : Measurable q := (Lp.stronglyMeasurable (G 0)).measurable.abs.add
    (Lp.stronglyMeasurable (G 1)).measurable.abs
  have hq0 (p : EuclideanPlane) : 0 ≤ q p := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hqL : MemLp q 2 (volume.restrict K) :=
    (((Lp.memLp (G 0)).norm.add (Lp.memLp (G 1)).norm).restrict K)
  let g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (q (complexPlaneCoordinates.symm z))
  let e : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal ‖f 0 n (complexPlaneCoordinates.symm z)‖+
      ENNReal.ofReal ‖f 1 n (complexPlaneCoordinates.symm z)‖
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    (hq.comp complexPlaneCoordinates.symm.continuous.measurable)
  have hgf : ∀ᵐ t ∂volume,
      (∫⁻ z in Q ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have ht := complex_coarea_L2_weight_finite hcoarea hv hw hLp hQ hq hqL
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hq0 _)] using ht
  have hgz : ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) = 0 :=
    complex_coarea_zero_product hcoarea hv hw hLp hF (ENNReal.measurable_ofReal.comp hq) (by
      have h0 := (scalarGradientRepresentative_ae W 0).filter_mono
        (ae_mono (Measure.restrict_le_self (s := complexPlaneCoordinates ⁻¹' F)))
      have h1 := (scalarGradientRepresentative_ae W 1).filter_mono
        (ae_mono (Measure.restrict_le_self (s := complexPlaneCoordinates ⁻¹' F)))
      filter_upwards [hz, h0, h1] with p hp hp0 hp1
      rcases hp with hp | hp
      · simp only [hp, norm_zero, ENNReal.ofReal_zero, mul_zero]
      · have hG0 : G 0 p = 0 := by simpa only [hp, PiLp.zero_apply] using hp0
        have hG1 : G 1 p = 0 := by simpa only [hp, PiLp.zero_apply] using hp1
        simp [q, hG0, hG1])
  have he (i : Fin 2) := complex_coarea_L2_errors hcoarea hv hw hLp hQ
    (f i) (hf i) (hfL i) (hfs i)
  have he0 : ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in Q ∩ {z | v z = t}, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0) := by
    filter_upwards [he 0, he 1] with t ht0 ht1
    have ht := ht0.add ht1
    simp only [add_zero] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact lintegral_add_left
      (ENNReal.measurable_ofReal.comp ((hf 0 n).norm.comp
        complexPlaneCoordinates.symm.continuous.measurable)) _
  apply full_level_null_image_of_approximation ψ hv hlim hQ hF.measurableSet hFQ
    (fun n => φ n ∘ complexPlaneCoordinates.symm)
    (fun n => ((hφ n).1.comp complexPlaneCoordinates.symm.contDiff).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun z hzQ => hφU.tendsto_at hzQ) g hg e ?_
    (complex_coarea_finite_levels hcoarea hv hw hLp hQ) hgf hgz he0
  intro n z
  have hp := complex_scalar_gradient_error (hφ n).1 (complexPlaneCoordinates.symm z)
    (G 0 (complexPlaneCoordinates.symm z)) (G 1 (complexPlaneCoordinates.symm z))
  rw [complexPlaneCoordinates.apply_symm_apply] at hp
  have hh := ENNReal.ofReal_le_ofReal hp
  change ENNReal.ofReal ‖fderiv ℝ (φ n ∘ complexPlaneCoordinates.symm) z‖ ≤
    ENNReal.ofReal (q (complexPlaneCoordinates.symm z) +
      (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|)) at hh
  have hsplit : ENNReal.ofReal (q (complexPlaneCoordinates.symm z) +
      (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|)) =
      g z+e n z := by
    calc
      _ = ENNReal.ofReal (q (complexPlaneCoordinates.symm z)) +
          ENNReal.ofReal (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|) :=
        ENNReal.ofReal_add (hq0 _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by
        dsimp only [g, e]
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        congr 1
        exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  exact hh.trans_eq hsplit


 theorem sobolev_height_level_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ) :
    ∀ᵐ t ∂volume, volume ((U ∘ complexPlaneCoordinates.symm) '' (F ∩ {z | v z = t})) = 0 :=
  sobolev_coordinate_level_null_image hcoarea ψ hv hlim hw hLp hF hQ hFQ hU W
    (hz.mono (fun _ hp => Or.inl hp))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_NullPairFromLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini for the compact image of a pair of continuous coordinates. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem null_pair_image_of_null_level_images
    {F : Set ℂ} (hF : IsCompact F) {u v : ℂ → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (hlevel : ∀ᵐ t ∂volume, volume (u '' (F ∩ {z | v z = t})) = 0) :
    volume ((fun z => (u z, v z)) '' F) = 0 := by
  have hcompact : IsCompact ((fun z => (u z, v z)) '' F) := hF.image (hu.prodMk hv)
  change (volume.prod volume) ((fun z => (u z, v z)) '' F) = 0
  rw [Measure.prod_apply_symm hcompact.measurableSet]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hlevel] with t ht
  have he : (fun x : ℝ => (x, t)) ⁻¹' ((fun z => (u z, v z)) '' F) =
      u '' (F ∩ {z | v z = t}) := by
    ext x
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨z, ⟨hz, congrArg Prod.snd he⟩, congrArg Prod.fst he⟩
    · rintro ⟨z, ⟨hz, hvz⟩, huz⟩
      exact ⟨z, hz, Prod.ext huz hvz⟩
  change volume ((fun x : ℝ => (x, t)) ⁻¹' ((fun z => (u z, v z)) '' F)) = 0
  rwa [he]


 theorem sobolev_height_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), v z)) '' F) = 0 := by
  apply null_pair_image_of_null_level_images hF (hU.comp complexPlaneCoordinates.symm.continuous) hv
  exact sobolev_height_level_null_image hcoarea ψ hv hlim hw hLp hF hQ hFQ hz hU W

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_HorizontalNullPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The companion trace pair with the ordinary horizontal coordinate.
The same proved level argument applies to the constant rotated homeomorphism. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem horizontal_weak_gradient :
    DeGiorgi.HasWeakGrad horizontalGradient (Complex.re ∘ complexPlaneCoordinates) univ := by
  intro i
  have h := weakPartial_of_smooth_on isOpen_univ horizontalLinear.contDiff.contDiffOn i
  convert h using 1
  · funext p
    fin_cases i <;> simp [horizontalGradient, ContinuousLinearMap.fderiv, horizontalLinear_apply]
  · rfl

 theorem horizontal_gradient_memLp (R : ℝ) (i : Fin 2) :
    MemLp (fun p => horizontalGradient p i) 2 (volume.restrict (ball 0 R)) := by
  let : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanPlane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  fin_cases i
  · exact memLp_const 1
  · exact memLp_const 0

 theorem horizontal_as_height :
    TendstoLocallyUniformly
      (fun (_ : ℕ) z => (Homeomorph.mulLeft₀ Complex.I Complex.I_ne_zero z).im) Complex.re atTop := by
  have h : TendstoLocallyUniformly (fun (_ : ℕ) z => z.re) Complex.re atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      (tendsto_const_nhds (x := (⟨Complex.re, Complex.continuous_re⟩ : C(ℂ, ℝ))))
  change TendstoLocallyUniformly (fun (_ : ℕ) z => (Complex.I*z).im) Complex.re atTop
  simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using h

 theorem sobolev_horizontal_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), W.weakGrad p = 0) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), z.re)) '' F) = 0 := by
  apply null_pair_image_of_null_level_images hF
    (hU.comp complexPlaneCoordinates.symm.continuous) Complex.continuous_re
  exact sobolev_coordinate_level_null_image hcoarea
    (fun _ => Homeomorph.mulLeft₀ Complex.I Complex.I_ne_zero) Complex.continuous_re
    horizontal_as_height horizontal_weak_gradient horizontal_gradient_memLp hF hQ hFQ hU W
    (hz.mono (fun _ hp => Or.inr hp))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalHorizontalNullPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The horizontal trace-pair lemma is local in the Sobolev coordinate.
A compact plateau reduces it to the global trace-pair statement. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem local_sobolev_horizontal_pair_null_image
    (hcoarea : PlanarSobolevCoarea)
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hKΩ : complexPlaneCoordinates ⁻¹' F ⊆ Ω)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U Ω)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), W.weakGrad p = 0) :
    volume ((fun z => (U (complexPlaneCoordinates.symm z), z.re)) '' F) = 0 := by
  let K := complexPlaneCoordinates ⁻¹' F
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  obtain ⟨η, V, hη, hsη, _, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro p hp
    apply hsub
    apply subset_tsupport η
    change η p ≠ 0
    rw [hone p hp]
    exact one_ne_zero
  obtain ⟨Ww⟩ := exists_global_compact_cutoff_witness hΩ W.memW1p hη hsη hsub
  have hg (i : Fin 2) := ae_restrict_of_ae_restrict_of_subset hKV
    (weakGrad_eq_on_cutoff_plateau hV hVΩ W Ww hone i)
  have hzero : ∀ᵐ p ∂volume.restrict K, Ww.weakGrad p = 0 := by
    filter_upwards [hz, hg 0, hg 1] with p hp hp0 hp1
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp_all
  have hh := sobolev_horizontal_pair_null_image hcoarea hF hQ hFQ
    (hη.continuous.mul hU) Ww hzero
  apply measure_mono_null (t := (fun z =>
    (η (complexPlaneCoordinates.symm z)*U (complexPlaneCoordinates.symm z), z.re)) '' F) ?_ hh
  rintro _ ⟨z, hzF, rfl⟩
  refine ⟨z, hzF, ?_⟩
  have hzK : complexPlaneCoordinates.symm z ∈ K := by
    change complexPlaneCoordinates (complexPlaneCoordinates.symm z) ∈ F
    rwa [complexPlaneCoordinates.apply_symm_apply]
  simp only [hone _ (hKV hzK), one_mul]

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
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ScalarModelConductivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual conductivity postcomposition stays in the retained model
class. Near maximality therefore bounds its first coefficient and both
terms of its proved global energy identity. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem complement_compact (M : CompactScalarModel G u) (hinf : OnePoint.infty ∈ G) :
    IsCompact (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ := by
  have hi : OnePoint.infty ∈ extendAtInfinity M.function '' G := ⟨_, hinf, rfl⟩
  have hK := (isCompact_finite_preimage M.image_open.isClosed_compl (not_not.mpr hi)).image
    complexPlaneCoordinates.symm.continuous
  convert hK using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · intro hx
    exact ⟨complexPlaneCoordinates x, hx, complexPlaneCoordinates.symm_apply_apply x⟩
  · rintro ⟨z, hz, rfl⟩
    change planeSphere (complexPlaneCoordinates.symm z) ∉ extendAtInfinity M.function '' G
    simpa only [planeSphere, ContinuousLinearEquiv.apply_symm_apply, mem_preimage, mem_compl_iff] using hz

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalZeroGradientConstant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous planar Sobolev function with zero weak gradient on a
connected open set is constant there and on its closure. The proved local
complex Weyl lemma reduces this to the holomorphic open mapping theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem constant_on_closure_of_zero_weak_gradient
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    {U : Set EuclideanPlane} (hU : IsOpen U) (hconn : IsConnected U)
    (hz : ∀ᵐ p ∂volume.restrict U, G p = 0) :
    ∃ c : ℝ, ∀ p ∈ closure U, u p = c := by
  let f : EuclideanPlane → ℂ := fun p => (u p : ℂ)
  let D : PlaneLocalWeakComplex f := {
    realGradient := G
    imagGradient := fun _ => 0
    real_weak := by simpa only [f, Complex.ofReal_re] using hw
    imag_weak := by
      intro i ψ hψ hs hsub
      simp [f]
    real_memLp := hLp
    imag_memLp := fun _ _ => MemLp.zero }
  have hz' : ∀ᵐ p ∂volume, p ∈ U → G p = 0 := by
    exact (ae_restrict_iff' hU.measurableSet).mp hz
  have hcr : ∀ᵐ p ∂volume, p ∈ U →
      D.realGradient p 0 = D.imagGradient p 1 ∧
      D.realGradient p 1 = -D.imagGradient p 0 := by
    filter_upwards [hz'] with p hp hpU
    simp [D, hp hpU]
  have hd := D.holomorphic_on_of_cauchyRiemann (Complex.continuous_ofReal.comp hu) hU hcr
  let V := complexPlaneCoordinates '' U
  have hV : IsOpen V := complexPlaneCoordinates.toHomeomorph.isOpenMap _ hU
  have hcV : IsConnected V := hconn.image _ complexPlaneCoordinates.continuous.continuousOn
  have ha : AnalyticOnNhd ℂ (fun z => f (complexPlaneCoordinates.symm z)) V :=
    fun z hz => hd.analyticAt (hV.mem_nhds hz)
  obtain ⟨c, hc⟩ := ha.eq_const_of_im_eq_const (c₀ := 0) (fun _ _ => rfl) hV hcV
  have hcu : U ⊆ {p | u p = c.re} := by
    intro p hp
    have hh := congrArg Complex.re (hc (complexPlaneCoordinates p) ⟨p, hp, rfl⟩)
    change u p = c.re
    simpa only [f, ContinuousLinearEquiv.symm_apply_apply, Complex.ofReal_re] using hh
  exact ⟨c.re, fun p hp => (closure_minimal hcu (isClosed_eq hu continuous_const)) hp⟩

 theorem constant_on_homeomorphic_disk
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (G : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad G u univ)
    (hLp : ∀ R i, MemLp (fun p => G p i) 2 (volume.restrict (Metric.ball 0 R)))
    (e : ℂ ≃ₜ EuclideanPlane) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hz : ∀ᵐ p ∂volume.restrict (e '' Metric.closedBall c r), G p = 0) :
    ∃ a : ℝ, ∀ p ∈ e '' Metric.closedBall c r, u p = a := by
  have hU : IsOpen (e '' Metric.ball c r) := e.isOpenMap _ Metric.isOpen_ball
  have hc : IsConnected (Metric.ball c r) :=
    ⟨⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  have hUc : IsConnected (e '' Metric.ball c r) := hc.image _ e.continuous.continuousOn
  have hzU : ∀ᵐ p ∂volume.restrict (e '' Metric.ball c r), G p = 0 :=
    hz.filter_mono (ae_mono (Measure.restrict_mono (image_mono Metric.ball_subset_closedBall) le_rfl))
  obtain ⟨a, ha⟩ := constant_on_closure_of_zero_weak_gradient hu G hw hLp hU hUc hzU
  rw [← e.image_closure, closure_ball c hr.ne'] at ha
  exact ⟨a, ha⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_HeightHorizontalNullPair
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed conductivity height and the ordinary horizontal
coordinate have a null-area joint trace on the omitted set. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ControlledHeight.horizontal_pair_null
    (hcoarea : PlanarSobolevCoarea) {R d : ℝ} (H : ControlledHeight R d)
    {F : Set ℂ} (hF : IsCompact F)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      heightLimitGradient H.error₀ H.error₁ p = 0) :
    volume ((fun z => (H.height z, z.re)) '' F) = 0 := by
  obtain ⟨S, hS⟩ := hF.isBounded.subset_ball 0
  let T := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFT : F ⊆ interior (closedBall (0 : ℂ) T) := by
    rw [interior_closedBall _ hT.ne']
    exact hS.trans (ball_subset_ball (le_max_left _ _))
  let K := complexPlaneCoordinates ⁻¹' F
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  obtain ⟨A, hA⟩ := hK.isBounded.subset_ball 0
  have hh := local_sobolev_horizontal_pair_null_image hcoarea hF
    (isCompact_closedBall 0 T) hFT isOpen_ball hA
    (H.height.continuous.comp complexPlaneCoordinates.continuous)
    (heightLimitWitness H.error₀ H.error₁
      (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A) hz
  simpa only [Function.comp_apply, complexPlaneCoordinates.apply_symm_apply] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_LipschitzTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinatewise scalar Lipschitz changes preserve null planar trace
pairs, including the constructed countable-value flattenings. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lipschitz_plane_image_null {A : ℝ × ℝ → ℝ × ℝ} {L : ℝ≥0}
    (hA : LipschitzWith L A) {S : Set (ℝ × ℝ)} (hS : volume S = 0) :
    volume (A '' S) = 0 := by
  have h := hA.hausdorffMeasure_image_le (d := 2) (by norm_num) S
  simpa only [hausdorffMeasure_prod_real, hS, mul_zero, nonpos_iff_eq_zero] using h

 theorem coordinate_lipschitz_pair_null {X : Type*} {S : Set X} {u v : X → ℝ}
    (hz : volume ((fun x => (u x, v x)) '' S) = 0)
    {A B : ℝ → ℝ} {L M : ℝ≥0} (hA : LipschitzWith L A) (hB : LipschitzWith M B) :
    volume ((fun x => (A (u x), B (v x))) '' S) = 0 := by
  have hmap : LipschitzWith (max (L*1) (M*1))
      (fun p : ℝ × ℝ => (A p.1, B p.2)) :=
    (hA.comp LipschitzWith.prod_fst).prodMk (hB.comp LipschitzWith.prod_snd)
  have he : (fun x => (A (u x), B (v x))) '' S =
      (fun p : ℝ × ℝ => (A p.1, B p.2)) '' ((fun x => (u x, v x)) '' S) := by
    rw [image_image]
  rw [he]
  exact lipschitz_plane_image_null hmap hz

 theorem flattened_pair_null {X : Type*} {S : Set X} {u v : X → ℝ}
    (hz : volume ((fun x => (u x, v x)) '' S) = 0)
    {O P : Set ℝ} (hO : MeasurableSet O) (hP : MeasurableSet P) :
    volume ((fun x => (flattenValues O (u x), flattenValues P (v x))) '' S) = 0 :=
  coordinate_lipschitz_pair_null hz (flattenValues_lipschitz hO) (flattenValues_lipschitz hP)

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
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelHeightTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two null trace-pair conclusions for every retained scalar of an
actual compact model and its constructed conductivity height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_trace_pairs (M : CompactScalarModel G u)
    (hcoarea : PlanarSobolevCoarea) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) (i : Fin m) :
    let F := complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
    let U := fun z : ℂ => sphereFromPlaneFunction (u i)
      (M.projection (planeSphere (complexPlaneCoordinates.symm z)))
    volume ((fun z => (U z, H.height z)) '' F) = 0 ∧
      volume ((fun z => (U z, z.re)) '' F) = 0 := by
  let F₀ := (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  let F := complexPlaneCoordinates '' F₀
  let U := fun p => sphereFromPlaneFunction (u i) (M.projection (planeSphere p))
  have hF₀ : IsCompact F₀ := M.complement_compact hinf
  have hF : IsCompact F := hF₀.image complexPlaneCoordinates.continuous
  have hpre : complexPlaneCoordinates ⁻¹' F = F₀ :=
    Set.preimage_image_eq F₀ complexPlaneCoordinates.injective
  obtain ⟨S, hS⟩ := hF.isBounded.subset_ball 0
  let T := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFQ : F ⊆ interior (closedBall (0 : ℂ) T) := by
    rw [interior_closedBall _ hT.ne']
    exact hS.trans (ball_subset_ball (le_max_left _ _))
  have hUc : Continuous U := M.scalar_continuous hu hs i
  have hWz (j : Fin 2) : ∀ᵐ p ∂volume.restrict F₀, (M.witness i).weakGrad p j = 0 := by
    apply (ae_restrict_iff' hF₀.measurableSet).mpr
    exact M.gradient_zero i j
  have hWzero : ∀ᵐ p ∂volume.restrict F₀, (M.witness i).weakGrad p = 0 := by
    filter_upwards [hWz 0, hWz 1] with p hp0 hp1
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext j
    fin_cases j <;> assumption
  constructor
  · apply sobolev_height_pair_null_image hcoarea H.approximants H.height.continuous H.height_limit
      H.weak_gradient (fun r j => (heightLimitWitness H.error₀ H.error₁
        (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient r).weakGrad_component_memLp j)
      hF (isCompact_closedBall 0 T) hFQ _ hUc (M.witness i)
    simpa only [hpre] using hHz
  · apply sobolev_horizontal_pair_null_image hcoarea hF (isCompact_closedBall 0 T) hFQ hUc (M.witness i)
    simpa only [hpre] using hWzero

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConcentratedCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoffs whose centers lie in a closed set and whose radii tend to
zero have a common finite tail vanishing near each point of its complement. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem concentrated_cutoffs_eventually_zero
    {X : Type*} [MetricSpace X] {B : Set X} (hB : IsClosed B)
    (c : ℕ → X) (hc : ∀ n, c n ∈ B) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → X → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (c n) (r n))
    {x : X} (hx : x ∉ B) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ y ∈ V, χ n y = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hx)
  have hsmall : ∀ᶠ n in atTop, r n < δ/2 := hr.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨ball x (δ/2), isOpen_ball, mem_ball_self (by linarith), N, ?_⟩
  intro n hn y hy
  by_contra hne
  have hyc := hs n hne
  have hcx : dist (c n) x < δ := by
    calc
      dist (c n) x ≤ dist (c n) y+dist y x := dist_triangle _ _ _
      _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using hyc.trans (hN n hn)) hy
      _ = δ := by ring
  exact (hball hcx) (hc n)

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
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelProjectionFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber identification for the actual coefficient-extremal scalar model.
Only the already cited geometric inputs construct its matched exhaustion. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem projection_fiber (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {p : Sphere} (hp : p ∉ extendAtInfinity M.function '' G) :
    M.projection ⁻¹' {M.projection p} =
      connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  exact (inverse_projection_component_eq_fiber hG hTD M.conformal.1 M.conformal.bijOn.injOn
    M.projection_continuous M.projection_inverse M.projection_outside
    C J hstrict hcover hd he hb hs hp).symm

 theorem projection_surjective (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ) :
    Surjective M.projection := by
  obtain ⟨C, J, hstrict, hcover, hd, he, hb, hs⟩ := exists_matched_jordan_exhaustion
    hsard hsch hG hconn hinf M.conformal.1 M.conformal.bijOn.injOn rfl
  intro q
  by_cases hq : q ∈ G
  · exact ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  · obtain ⟨b, p, hp, hsource, htarget, _⟩ := corresponding_target_end_of_source hG
      M.conformal.1 M.conformal.bijOn.injOn C J hstrict hcover hd he hb hs hq
    refine ⟨p, ?_⟩
    have hmem : M.projection p ∈ connectedComponentIn Gᶜ q := by
      rw [hsource]
      apply mem_iInter.mpr
      intro n
      have hfront : ((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C n).disk (b n))) ⊆ G := by
        intro x hx
        apply (C n).subset
        have hh : x ∈ frontier (C n).carrier := by
          rw [SmoothJordanCore.carrier, frontier_closedJordanCore (C n).disk (C n).disjoint]
          exact mem_iUnion.mpr ⟨b n, hx⟩
        simpa only [(C n).isCompact.isClosed.closure_eq] using frontier_subset_closure hh
      apply inverse_projection_matched_cap hG M.projection_continuous
        M.projection_inverse M.projection_outside ((C n).disk (b n)) (J n (b n))
        hfront (hb n (b n)) (hs n (b n))
      exact mem_image_of_mem _ (mem_iInter.mp (htarget ▸ mem_connectedComponentIn hp) n)
    have hsingle : connectedComponentIn Gᶜ q = {q} :=
      (hTD _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn).eq_singleton_of_mem
        (mem_connectedComponentIn hq)
    simpa only [hsingle, mem_singleton_iff] using hmem

 theorem projection_closed (M : CompactScalarModel G u) : IsClosedMap M.projection :=
  M.projection_continuous.isClosedMap

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedMapDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous scalar constant on each compact fiber descends through
a closed quotient. Only continuity along the relevant fiber is needed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_section_continuousAt_of_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (s : Y → X) (hs : ∀ y, P (s y) = y)
    {a : X → ℝ} {q : Y} {v : ℝ}
    (ha : ∀ z, P z = q → ContinuousAt a z)
    (hc : ∀ z, P z = q → a z = v) :
    ContinuousAt (a ∘ s) q ∧ a (s q) = v := by
  have hvalue : a (s q) = v := hc _ (hs q)
  refine ⟨?_, hvalue⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let U := interior (a ⁻¹' ball v ε)
  have hU : IsOpen U := isOpen_interior
  have hfiber : P ⁻¹' {q} ⊆ U := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hn : ball v ε ∈ 𝓝 (a z) := by rw [hc z hz]; exact ball_mem_nhds _ hε
    exact (ha z hz).preimage_mem_nhds hn
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hqV : q ∈ kernImage P U := fun _ hz => hfiber hz
  filter_upwards [hV.mem_nhds hqV] with y hy
  have hsy : s y ∈ U := hy (hs y)
  have hnear := interior_subset hsy
  simpa only [mem_preimage, mem_ball, comp_apply, hvalue] using hnear

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ModelHeightComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous zero-gradient height is constant on every actual
complementary component of a retained deformed circle model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {v : ℂ → ℝ} (hv : Continuous v)
    (V : EuclideanPlane → EuclideanPlane)
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    (hz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      V p = 0)
    {p q : EuclideanPlane} (hp : p ∉ physicalPlaneDomain (extendAtInfinity M.function '' G))
    (hq : planeSphere q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere p)) :
    v (complexPlaneCoordinates p) = v (complexPlaneCoordinates q) := by
  let Ω := extendAtInfinity M.function '' G
  let e := M.deformation.onePointCongr
  have he : e '' M.roundDomain = Ω := M.image_eq.symm
  have hec : e '' M.roundDomainᶜ = Ωᶜ := by rw [e.image_compl, he]
  have hp0 : e.symm (planeSphere p) ∈ M.roundDomainᶜ := by
    intro hh
    apply hp
    change planeSphere p ∈ Ω
    rw [← he]
    exact ⟨_, hh, e.apply_symm_apply _⟩
  let K := connectedComponentIn M.roundDomainᶜ (e.symm (planeSphere p))
  have hKimage : e '' K = connectedComponentIn Ωᶜ (planeSphere p) := by
    simpa only [hec, e.apply_symm_apply] using e.image_connectedComponentIn hp0
  have hpk : e.symm (planeSphere p) ∈ K := mem_connectedComponentIn hp0
  have hqk : e.symm (planeSphere q) ∈ K := by
    have hq' : planeSphere q ∈ e '' K := by rwa [hKimage]
    obtain ⟨a, ha, haq⟩ := hq'
    simpa only [← haq, e.symm_apply_apply] using ha
  rcases M.round_circle.2.2 (e.symm (planeSphere p)) hp0 with hsingle | hround
  · obtain ⟨a, ha⟩ := hsingle
    change K = {a} at ha
    have hpq : e.symm (planeSphere p) = e.symm (planeSphere q) := by
      rw [ha] at hpk hqk
      exact (mem_singleton_iff.mp hpk).trans (mem_singleton_iff.mp hqk).symm
    have hh := congrArg e hpq
    simp only [e.apply_symm_apply] at hh
    exact congrArg v (OnePoint.coe_injective hh)
  · change IsRoundClosedDisk K at hround
    have hiΩ : OnePoint.infty ∈ Ω := ⟨_, hinf, rfl⟩
    have hiround : OnePoint.infty ∈ M.roundDomain := by
      rw [← he] at hiΩ
      obtain ⟨a, ha, hai⟩ := hiΩ
      have haInf : a = OnePoint.infty := by
        apply e.injective
        exact hai
      rwa [haInf] at ha
    have hiK : OnePoint.infty ∉ K := by
      intro hh
      exact (connectedComponentIn_subset _ _ hh) hiround
    obtain ⟨c, r, hr, hK⟩ := isRoundClosedDisk_eq_euclidean hround hiK
    let E : ℂ ≃ₜ EuclideanPlane := M.deformation.trans complexPlaneCoordinates.symm.toHomeomorph
    have hE (z : ℂ) : planeSphere (E z) = e (z : Sphere) := by
      change ((complexPlaneCoordinates (complexPlaneCoordinates.symm (M.deformation z)) : ℂ) : Sphere) = _
      rw [complexPlaneCoordinates.apply_symm_apply]
      rfl
    have hsub : E '' Metric.closedBall c r ⊆ (physicalPlaneDomain Ω)ᶜ := by
      rintro a ⟨z, hz', rfl⟩
      change planeSphere (E z) ∈ Ωᶜ
      rw [hE, ← hec]
      apply mem_image_of_mem
      apply connectedComponentIn_subset M.roundDomainᶜ (e.symm (planeSphere p))
      change (z : Sphere) ∈ K
      rw [hK]
      exact ⟨z, hz', rfl⟩
    have hzE : ∀ᵐ a ∂volume.restrict (E '' Metric.closedBall c r), V a = 0 :=
      hz.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    obtain ⟨a, ha⟩ := constant_on_homeomorphic_disk (hv.comp complexPlaneCoordinates.continuous)
      V hw hLp E c hr hzE
    have hmem (t : EuclideanPlane) (ht : e.symm (planeSphere t) ∈ K) :
        t ∈ E '' Metric.closedBall c r := by
      have hback : e.symm (planeSphere t) =
          ((M.deformation.symm (complexPlaneCoordinates t) : ℂ) : Sphere) := rfl
      rw [hback, hK, OnePoint.coe_injective.mem_set_image] at ht
      refine ⟨M.deformation.symm (complexPlaneCoordinates t), ht, ?_⟩
      change complexPlaneCoordinates.symm
        (M.deformation (M.deformation.symm (complexPlaneCoordinates t))) = t
      rw [M.deformation.apply_symm_apply, complexPlaneCoordinates.symm_apply_apply]
    exact (ha p (hmem p hpk)).trans (ha q (hmem q hqk)).symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelHeightDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed conductivity height descends continuously through
the actual source projection, including every nonpoint end. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_constant_on_sphere_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    {p q : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hq : q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p) :
    H.height (finiteCoord p) = H.height (finiteCoord q) := by
  have hqout := connectedComponentIn_subset _ _ hq
  cases p using OnePoint.rec with
  | infty => exact (hp ⟨_, hinf, rfl⟩).elim
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact (hqout ⟨_, hinf, rfl⟩).elim
    | coe w =>
      have hp' : complexPlaneCoordinates.symm z ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply] using hp
      have hq' : planeSphere (complexPlaneCoordinates.symm w) ∈
          connectedComponentIn (extendAtInfinity M.function '' G)ᶜ (planeSphere (complexPlaneCoordinates.symm z)) := by
        simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using hq
      simpa only [finiteCoord_coe, complexPlaneCoordinates.apply_symm_apply] using
        M.height_constant_on_components hinf H.height.continuous
          (heightLimitGradient H.error₀ H.error₁) H.weak_gradient
          (fun r i => (heightLimitWitness H.error₀ H.error₁
            (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient r).weakGrad_component_memLp i)
          hHz hp' hq'

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelSourceTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The null trace pairs on the actual target complement pull back to
all source ends through the constructed surjective projection. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem section_target_complement (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    let p := invFun M.projection (q : Sphere)
    finiteCoord p ∈ complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ∧
      planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p ∧
      M.projection p = (q : Sphere) := by
  let p := invFun M.projection (q : Sphere)
  have hpq : M.projection p = (q : Sphere) :=
    rightInverse_invFun (M.projection_surjective hsard hsch hG hconn hinf hTD) _
  have hpout : p ∉ extendAtInfinity M.function '' G := by
    rintro ⟨x, hx, he⟩
    have hh : M.projection p = x := by rw [← he, M.projection_inverse x hx]
    exact hq ((hh.symm.trans hpq) ▸ hx)
  have hpinf : p ≠ OnePoint.infty := by
    rintro h
    exact hpout (h.symm ▸ ⟨_, hinf, rfl⟩)
  have hplane : planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p := by
    simpa only [planeSphere, complexPlaneCoordinates.apply_symm_apply] using coe_finiteCoord hpinf
  refine ⟨?_, hplane, hpq⟩
  refine ⟨complexPlaneCoordinates.symm (finiteCoord p), ?_, complexPlaneCoordinates.apply_symm_apply _⟩
  simpa only [physicalPlaneDomain, mem_compl_iff, mem_preimage, hplane] using hpout

 theorem source_height_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) (i : Fin m) :
    let B := {q : ℂ | (q : Sphere) ∉ G}
    volume ((fun q : ℂ => (sphereFromPlaneFunction (u i) (q : Sphere),
      M.heightSection H (q : Sphere))) '' B) = 0 ∧
    volume ((fun q : ℂ => (sphereFromPlaneFunction (u i) (q : Sphere),
      M.horizontalSection (q : Sphere))) '' B) = 0 := by
  obtain ⟨hheight, hreal⟩ := M.height_trace_pairs hcoarea hinf hu hs H hHz i
  constructor
  · apply measure_mono_null (t := (fun z : ℂ =>
      (sphereFromPlaneFunction (u i) (M.projection (planeSphere (complexPlaneCoordinates.symm z))), H.height z)) ''
        (complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)) ?_ hheight
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hp, hplane, hpq⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
    refine ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, ?_⟩
    simp only [hplane, hpq, heightSection]
  · apply measure_mono_null (t := (fun z : ℂ =>
      (sphereFromPlaneFunction (u i) (M.projection (planeSphere (complexPlaneCoordinates.symm z))), z.re)) ''
        (complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ)) ?_ hreal
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hp, hplane, hpq⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
    refine ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, ?_⟩
    simp only [hplane, hpq, horizontalSection]

 theorem source_height_horizontal_pair (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0) :
    volume ((fun q : ℂ => (M.heightSection H (q : Sphere),
      M.horizontalSection (q : Sphere))) '' {q : ℂ | (q : Sphere) ∉ G}) = 0 := by
  let F := complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ
  have hF : IsCompact F := (M.complement_compact hinf).image complexPlaneCoordinates.continuous
  have hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      heightLimitGradient H.error₀ H.error₁ p = 0 := by
    rwa [Set.preimage_image_eq _ complexPlaneCoordinates.injective]
  have hh := H.horizontal_pair_null hcoarea hF hz
  apply measure_mono_null (t := (fun z => (H.height z, z.re)) '' F) ?_ hh
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨hp, _, _⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
  exact ⟨finiteCoord (invFun M.projection (q : Sphere)), hp, rfl⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ScalarQuotientDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous scalar constant on closed quotient fibers descends
continuously. An exact zero neighborhood also descends when its fiber
is a singleton. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_scalar_descent_continuous
    {X Y : Type*} [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (hsurj : Surjective P)
    {a : X → ℝ} (ha : Continuous a)
    (hc : ∀ x y, P x = P y → a x = a y) :
    Continuous (fun y => a (invFun P y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (closed_map_section_continuousAt_of_fiber hP (invFun P)
    (rightInverse_invFun hsurj) (fun x _ => ha.continuousAt)
    (fun x hx => hc x (invFun P y) (hx.trans (rightInverse_invFun hsurj y).symm))).1

 theorem scalar_descent_on_projection
    {X Y : Type*} [Nonempty X] {P : X → Y} (hsurj : Surjective P) {a : X → ℝ}
    (hc : ∀ x y, P x = P y → a x = a y) (x : X) :
    a (invFun P (P x)) = a x := hc _ _ (rightInverse_invFun hsurj _)

 theorem closed_map_zero_neighborhood_descends
    {X Y : Type*} [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (hsurj : Surjective P)
    {p : X} (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ}
    (ha : ∀ᶠ x in 𝓝 p, a x = 0) :
    ∀ᶠ y in 𝓝 (P p), a (invFun P y) = 0 := by
  obtain ⟨U, hUzero, hU, hpU⟩ := mem_nhds_iff.mp ha
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hpV : P p ∈ kernImage P U := by
    intro x hx
    have hxp : x = p := by
      have hh : x ∈ P ⁻¹' {P p} := hx
      simpa only [hfiber, mem_singleton_iff] using hh
    exact hxp ▸ hpU
  filter_upwards [hV.mem_nhds hpV] with y hy
  exact hUzero (hy (rightInverse_invFun hsurj y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelScalarDescent
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact continuous target scalar constant on the actual omitted
components yields a compact continuous scalar on the source sphere. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_constant_on_fibers (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : Sphere → ℝ}
    (ha : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p, a p = a q) :
    ∀ p q, M.projection p = M.projection q → a p = a q := by
  intro p q hpq
  by_cases hp : p ∈ extendAtInfinity M.function '' G
  · obtain ⟨x, hx, rfl⟩ := hp
    have hp := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hx).mp
      (hpq.symm.trans (M.projection_inverse x hx))
    rw [hp]
  · apply ha p hp q
    rw [← M.projection_fiber hsard hsch hG hconn hinf hTD hp]
    exact hpq.symm

 theorem compact_scalar_descent (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hvs : HasCompactSupport v)
    (hc : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p,
        sphereFromPlaneFunction v p = sphereFromPlaneFunction v q) :
    let a := fun q => sphereFromPlaneFunction v (invFun M.projection q)
    Continuous a ∧
      HasCompactSupport (fun z : ℂ => a (z : Sphere)) ∧
      (∀ p ∈ G, a p = sphereFromPlaneFunction v (extendAtInfinity M.function p)) := by
  let a := sphereFromPlaneFunction v
  have ha : Continuous a := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ hv.continuousOn hvs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hs := M.projection_surjective hsard hsch hG hconn hinf hTD
  have hf := M.scalar_constant_on_fibers hsard hsch hG hconn hinf hTD hc
  have hi : M.projection OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
  have hfi : M.projection ⁻¹' {M.projection OnePoint.infty} = {OnePoint.infty} := by
    ext p
    simpa only [hi, mem_preimage, mem_singleton_iff, extendAtInfinity_infty] using
      inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf (y := p)
  have hz : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), a p = 0 := by
    have hsphere : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), p ∉ planeSphere '' tsupport v :=
      ((hvs.isCompact.image continuous_planeSphere).isClosed.isOpen_compl.mem_nhds (by
        rintro ⟨x, _, hx⟩
        exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hx))
    filter_upwards [hsphere] with p hp
    cases p using OnePoint.rec with
    | infty => simp [a, sphereFromPlaneFunction]
    | coe z =>
      have hvz : complexPlaneCoordinates.symm z ∉ tsupport v := by
        intro hx
        apply hp
        exact ⟨_, hx, by simp only [planeSphere, complexPlaneCoordinates.apply_symm_apply]⟩
      simpa only [a, sphereFromPlaneFunction_coe] using image_eq_zero_of_notMem_tsupport hvz
  have hzero := closed_map_zero_neighborhood_descends M.projection_closed hs hfi hz
  rw [hi] at hzero
  refine ⟨closed_map_scalar_descent_continuous M.projection_closed hs ha hf, ?_, ?_⟩
  · rw [hasCompactSupport_iff_eventuallyEq]
    exact OnePoint.tendsto_coe_infty.eventually hzero
  · intro p hp
    have hh := scalar_descent_on_projection hs hf (extendAtInfinity M.function p)
    simpa only [M.projection_inverse p hp] using hh

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelScalarPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
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

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_scalar_pullback (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hvs : HasCompactSupport v)
    (V : DeGiorgi.MemW1pWitness 2 v univ)
    (hc : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p,
        sphereFromPlaneFunction v p = sphereFromPlaneFunction v q) :
    let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
    Continuous w ∧ HasCompactSupport w ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 w (physicalPlaneDomain G),
        (∫ x in physicalPlaneDomain G, W.weakGrad x 0^2+W.weakGrad x 1^2) ≤
          ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
            V.weakGrad x 0^2+V.weakGrad x 1^2 := by
  obtain ⟨hcont, hsupp, hvalue⟩ := M.compact_scalar_descent hsard hsch hG hconn hinf hTD hv hvs hc
  let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
  have hw : Continuous w := hcont.comp continuous_planeSphere
  have hws : HasCompactSupport w := hsupp.comp_homeomorph complexPlaneCoordinates.toHomeomorph
  obtain ⟨hfc, hmap, fi, hfic, hfimap, hl, hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.image_open hp, hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp, hmap, hr, hl⟩
  have hfi : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hi : OnePoint.infty ∈ extendAtInfinity M.function '' G := ⟨_, hinf, rfl⟩
  have hL : MemLp w 2 (volume.restrict (physicalPlaneDomain G)) :=
    (hw.memLp_of_hasCompactSupport hws).restrict _
  obtain ⟨W, hW⟩ := sobolev_conformal_transport heq M.image_open hG hi hfi hfic hv hvs V
    (v := w) (fun x hx => by
      rw [planeInverseTransport_extendAtInfinity]
      exact hvalue (planeSphere x) hx) hL
  exact ⟨hw, hws, W, hW⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactHeightPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The flattened height, cut off beyond the actual omitted set, is a
compact continuous Sobolev test on the source. The constancy on holes is
proved from the constructed height. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_cutoff_constant_on_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    (hη : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1)
    {p q : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hq : q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p) :
    sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x))) p =
      sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x))) q := by
  have hheight := M.height_constant_on_sphere_components hinf H hHz hp hq
  have hqout := connectedComponentIn_subset _ _ hq
  cases p using OnePoint.rec with
  | infty => exact (hp ⟨_, hinf, rfl⟩).elim
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact (hqout ⟨_, hinf, rfl⟩).elim
    | coe w =>
      have hz : complexPlaneCoordinates.symm z ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply] using hp
      have hw : complexPlaneCoordinates.symm w ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply, mem_compl_iff] using hqout
      simp only [sphereFromPlaneFunction_coe, hη _ hz, hη _ hw,
        complexPlaneCoordinates.apply_symm_apply, one_mul]
      exact congrArg T (by simpa only [finiteCoord_coe] using hheight)

 theorem compact_flattened_height_pullback (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (O : Set ℝ) (hO : MeasurableSet O) (A : ℝ)
    (W : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ H.height ∘ complexPlaneCoordinates) (Metric.ball 0 A))
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηA : tsupport η ⊆ Metric.ball 0 A)
    (hηF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1) :
    let v := fun x => η x*flattenValues O (H.height (complexPlaneCoordinates x))
    let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
    Continuous w ∧ HasCompactSupport w ∧
      Nonempty (DeGiorgi.MemW1pWitness 2 w (physicalPlaneDomain G)) := by
  let v := fun x => η x*flattenValues O (H.height (complexPlaneCoordinates x))
  have hv : Continuous v := hη.continuous.mul
    ((flattenValues_lipschitz hO).continuous.comp (H.height.continuous.comp complexPlaneCoordinates.continuous))
  have hvs : HasCompactSupport v := hηs.mul_right
  obtain ⟨V⟩ := exists_global_compact_cutoff_witness Metric.isOpen_ball W.memW1p hη hηs hηA
  obtain ⟨hw, hws, Ww, _⟩ := M.compact_scalar_pullback hsard hsch hG hconn hinf hTD hv hvs V
    (fun p hp q hq => M.height_cutoff_constant_on_components hinf H hHz (flattenValues O) η hηF hp hq)
  exact ⟨hw, hws, ⟨Ww⟩⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ModelCompactHeightTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact descended height has exactly the previously constructed
trace at every source end. Compactification does not change null-pair data. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_trace (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    (hη : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x)))
      (invFun M.projection (q : Sphere)) = T (M.heightSection H (q : Sphere)) := by
  obtain ⟨hp, hplane, _⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
  let p := invFun M.projection (q : Sphere)
  have hout : complexPlaneCoordinates.symm (finiteCoord p) ∉
      physicalPlaneDomain (extendAtInfinity M.function '' G) := by
    obtain ⟨x, hx, heq⟩ := hp
    have he : complexPlaneCoordinates.symm (finiteCoord p) = x := by
      rw [← heq, complexPlaneCoordinates.symm_apply_apply]
    simpa only [he, mem_compl_iff] using hx
  change sphereFromPlaneFunction _ p = _
  change planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p at hplane
  conv_lhs => rw [← hplane]
  simp only [planeSphere, sphereFromPlaneFunction_coe,
    hη _ hout, one_mul, complexPlaneCoordinates.apply_symm_apply, heightSection]
  rfl

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableConstantPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Changing one coordinate inside countably many sets where the other
coordinate is constant preserves the null-area trace-pair condition. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem pair_null_of_countable_constant_cover
    {X : Type*} {T : Set X} (S : ℕ → Set X) (u v w : X → ℝ)
    (hold : volume ((fun x => (u x, v x)) '' T) = 0)
    (hsame : ∀ x ∈ T, x ∉ ⋃ n, S n → w x = v x)
    (hconstant : ∀ n, ∃ a : ℝ, ∀ x ∈ T ∩ S n, u x = a) :
    volume ((fun x => (u x, w x)) '' T) = 0 := by
  choose a ha using hconstant
  have hline (n : ℕ) : volume (({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    change (volume.prod volume) _ = 0
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  have hunion : volume (⋃ n, ({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 :=
    measure_iUnion_null hline
  apply measure_mono_null (t := ((fun x => (u x, v x)) '' T) ∪
    ⋃ n, ({a n} : Set ℝ) ×ˢ (univ : Set ℝ)) ?_ (measure_union_null hold hunion)
  rintro _ ⟨x, hx, rfl⟩
  by_cases hs : x ∈ ⋃ n, S n
  · obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    exact Or.inr (mem_iUnion.mpr ⟨n, by simp only [mem_prod, mem_singleton_iff, mem_univ, and_true]; exact ha n x ⟨hx, hn⟩⟩)
  · exact Or.inl ⟨x, hx, by simp only [hsame x hx hs]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PriorityTracePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Priority modification preserves every trace pair whose other
coordinate is constant on its cutoff supports. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem priorityInfiniteValue_eq_outside_support
    {X : Type*} (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (v : X → ℝ)
    {x : X} (hx : x ∉ ⋃ n, support (χ n)) :
    priorityInfiniteValue (fun n => χ n x) c (v x) = v x := by
  have hzero (n : ℕ) : χ n x = 0 := by
    by_contra hh
    exact hx (mem_iUnion.mpr ⟨n, hh⟩)
  simp only [priorityInfiniteValue, priorityWeight, hzero, zero_mul, tsum_zero,
    sub_zero, one_mul, add_zero]

 theorem priority_trace_pair_null
    {X : Type*} {T : Set X} (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (u v : X → ℝ)
    (hold : volume ((fun x => (u x, v x)) '' T) = 0)
    (hconstant : ∀ n, ∃ a : ℝ, ∀ x ∈ T ∩ support (χ n), u x = a) :
    volume ((fun x => (u x, priorityInfiniteValue (fun n => χ n x) c (v x))) '' T) = 0 := by
  apply pair_null_of_countable_constant_cover (fun n => support (χ n)) u v
    (fun x => priorityInfiniteValue (fun n => χ n x) c (v x)) hold
    (fun x _ hx => priorityInfiniteValue_eq_outside_support χ c v hx) hconstant

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SphereTracePairNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact trace-pair transfer between the finite plane and a sphere
complement avoiding infinity. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem sphere_trace_pair_null_of_plane {G : Set Sphere}
    (hinf : OnePoint.infty ∈ G) (a b : Sphere → ℝ)
    (h : volume ((fun z : ℂ => (a (z : Sphere),b (z : Sphere))) ''
      {z : ℂ | (z : Sphere) ∉ G}) = 0) :
    volume ((fun z => (a z,b z)) '' Gᶜ) = 0 := by
  apply measure_mono_null (t := (fun z : ℂ => (a (z : Sphere),b (z : Sphere))) ''
    {z : ℂ | (z : Sphere) ∉ G}) ?_ h
  rintro _ ⟨z, hz, rfl⟩
  cases z using OnePoint.rec with
  | infty => exact (hz hinf).elim
  | coe z => exact ⟨z,hz,rfl⟩

 theorem sphereFromPlaneFunction_flatten (O : Set ℝ) (u : EuclideanPlane → ℝ) (p : Sphere) :
    sphereFromPlaneFunction (flattenValues O ∘ u) p = flattenValues O (sphereFromPlaneFunction u p) := by
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction, flattenValues_zero]
  | coe z => simp only [sphereFromPlaneFunction_coe, Function.comp_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AppendedScalarPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair-nullity for the exact finite list obtained by adjoining two
scalar tests. The first two coordinates are the new tests. -/
open Set Function MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem trace_pair_null_symm {X : Type*} {S : Set X} {u v : X → ℝ}
    (h : volume ((fun x => (u x, v x)) '' S) = 0) :
    volume ((fun x => (v x, u x)) '' S) = 0 := by
  have he : (fun x : ℝ × ℝ => (x.2,x.1)) = Prod.swap := by
    funext x
    cases x
    rfl
  have hs : LipschitzWith (1 : ℝ≥0) (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    rw [← he]
    simpa only [max_self] using (LipschitzWith.prod_snd (α := ℝ) (β := ℝ)).prodMk LipschitzWith.prod_fst
  have hh := lipschitz_plane_image_null hs h
  simpa only [image_image, Function.comp_def, Prod.swap_prod_mk] using hh

 theorem appendScalarPair_pair_null {X : Type*} {S : Set X} {m : ℕ}
    (u : Fin m → X → ℝ) (p q : X → ℝ)
    (hu : ∀ i j, i ≠ j → volume ((fun x => (u i x,u j x)) '' S) = 0)
    (hp : ∀ i, volume ((fun x => (u i x,p x)) '' S) = 0)
    (hq : ∀ i, volume ((fun x => (u i x,q x)) '' S) = 0)
    (hqp : volume ((fun x => (q x,p x)) '' S) = 0) :
    ∀ i j, i ≠ j → volume ((fun x =>
      (appendScalarPair u p q i x,appendScalarPair u p q j x)) '' S) = 0 := by
  intro i j hij
  refine Fin.cases ?_ (fun a => ?_) i hij
  · refine Fin.cases (fun h => (h rfl).elim) (fun b _ => ?_) j
    refine Fin.cases ?_ (fun k => ?_) b
    · exact hqp
    · exact trace_pair_null_symm (hq k)
  · refine Fin.cases (fun _ => ?_) (fun b hab => ?_) j
    · refine Fin.cases ?_ (fun k => ?_) a
      · exact trace_pair_null_symm hqp
      · exact hq k
    · refine Fin.cases ?_ (fun k => ?_) a hab
      · refine Fin.cases (fun h => (h rfl).elim) (fun l _ => ?_) b
        exact trace_pair_null_symm (hp l)
      · refine Fin.cases (fun _ => ?_) (fun l h => ?_) b
        · exact hp k
        · exact hu k l (fun he => h (congrArg (fun n => n.succ.succ) he))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorityFinite
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite recursive interpolation with the
priority-weight formula, for passage from local finite sums to the
countable interpolation. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {E : Type*}

 theorem priorityBlend_append (L M : List ((E → ℝ) × ℝ)) (X : E → ℝ) :
    priorityBlend (L++M) X = priorityBlend L (priorityBlend M X) := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [List.cons_append, priorityBlend, ih]

 theorem priorityResidual_append (L M : List ((E → ℝ) × ℝ)) (p : E) :
    priorityResidual (L++M) p = priorityResidual L p*priorityResidual M p := by
  induction L with
  | nil => simp [priorityResidual]
  | cons e L ih => simp only [List.cons_append, priorityResidual, ih] <;> ring

 theorem priorityBlend_sub (L : List ((E → ℝ) × ℝ)) (X Y : E → ℝ) (p : E) :
    priorityBlend L X p-priorityBlend L Y p = priorityResidual L p*(X p-Y p) := by
  induction L with
  | nil => simp [priorityBlend, priorityResidual]
  | cons e L ih =>
    change e.1 p*e.2+(1-e.1 p)*priorityBlend L X p-
      (e.1 p*e.2+(1-e.1 p)*priorityBlend L Y p) =
      (1-e.1 p)*priorityResidual L p*(X p-Y p)
    calc
      _ = (1-e.1 p)*(priorityBlend L X p-priorityBlend L Y p) := by ring
      _ = _ := by rw [ih]; ring

 theorem priorityList_succ (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    priorityList χ c (n+1) = priorityList χ c n++[(χ n,c n)] := by
  simp [priorityList, List.range_succ]

 theorem priorityList_residual (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (n : ℕ) (p : E) :
    priorityResidual (priorityList χ c n) p = priorityRemainder (fun i => χ i p) n := by
  induction n with
  | zero => simp [priorityList, priorityResidual, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityResidual_append, ih, priorityRemainder_succ]
    simp [priorityResidual]

 theorem priorityList_value (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) (n : ℕ) (p : E) :
    priorityBlend (priorityList χ c n) X p =
      priorityRemainder (fun i => χ i p) n*X p +
        ∑ i ∈ Finset.range n, priorityWeight (fun j => χ j p) i*c i := by
  induction n with
  | zero => simp [priorityList, priorityBlend, priorityRemainder]
  | succ n ih =>
    rw [priorityList_succ, priorityBlend_append]
    have h := priorityBlend_sub (priorityList χ c n) (priorityBlend [(χ n,c n)] X) X p
    rw [priorityList_residual, ih] at h
    simp only [priorityBlend] at h
    rw [priorityRemainder_succ, Finset.sum_range_succ]
    dsimp only [priorityBlend, priorityWeight] at h ⊢
    nlinarith only [h]

 theorem priorityInfiniteValue_eq_finite {χ : ℕ → E → ℝ} (c : ℕ → ℝ) (X : E → ℝ)
    {N : ℕ} {p : E} (hz : ∀ n, N ≤ n → χ n p = 0) :
    priorityInfiniteValue (fun n => χ n p) c (X p) = priorityBlend (priorityList χ c N) X p := by
  have hw (n : ℕ) (hn : n ∉ Finset.range N) : priorityWeight (fun i => χ i p) n = 0 := by
    rw [priorityWeight, hz n (by simpa only [Finset.mem_range, not_lt] using hn), zero_mul]
  have hs : (∑' n, priorityWeight (fun i => χ i p) n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n := tsum_eq_sum hw
  have hsc : (∑' n, priorityWeight (fun i => χ i p) n*c n) =
      ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i p) n*c n :=
    tsum_eq_sum (fun n hn => by rw [hw n hn, zero_mul])
  rw [priorityInfiniteValue, hs, hsc, priorityWeight_sum, priorityList_value]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ModelScalarEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source horizontal section is smooth off the dust and has
finite differential energy on each bounded source region. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem horizontalSection_plane_smooth (M : CompactScalarModel G u) (hG : IsOpen G) :
    ContDiffOn ℝ ∞ (fun z : ℂ => M.horizontalSection (z : Sphere)) {z : ℂ | (z : Sphere) ∈ G} := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt
  have hc : ContDiffOn ℝ ∞ M.function D := (hf.contDiffOn hD).restrict_scalars ℝ
  apply (Complex.reCLM.contDiff.comp_contDiffOn hc).congr
  intro z hz
  simpa only [Function.comp_apply, Complex.reCLM_apply, extendAtInfinity_coe, finiteCoord_coe] using
    M.horizontalSection_on_domain hz

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrioritySmooth
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The priority formula is smooth off the closed source dust because
its shrinking cutoff supports have a common locally vanishing tail. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityBlend_contDiffAt {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hL : ∀ e ∈ L, ContDiffAt ℝ ∞ e.1 p) :
    ContDiffAt ℝ ∞ (priorityBlend L X) p := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    exact (he.mul contDiffAt_const).add ((contDiffAt_const.sub he).mul
      (ih (fun a ha => hL a (by simp [ha]))))

 theorem priorityInfiniteValue_contDiffAt
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hχ : ∀ n, ContDiffAt ℝ ∞ (χ n) p)
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    ContDiffAt ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p := by
  obtain ⟨N, hN⟩ := hz
  have hL : ∀ e ∈ priorityList χ c N, ContDiffAt ℝ ∞ e.1 p := by
    intro e he
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact hχ n
  apply (priorityBlend_contDiffAt hX hL).congr_of_eventuallyEq
  filter_upwards [hN] with q hq
  exact priorityInfiniteValue_eq_finite c X hq

 theorem priorityInfiniteValue_smooth_off_dust
    {B : Set E} (hB : IsClosed B) (b : ℕ → E) (hb : ∀ n, b n ∈ B)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → E → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hs : ∀ n, support (χ n) ⊆ Metric.ball (b n) (r n))
    (c : ℕ → ℝ) (X : E → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ) :
    ContDiffOn ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) Bᶜ := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply priorityInfiniteValue_contDiffAt χ c X
    ((hX p hp).contDiffAt (hB.isOpen_compl.mem_nhds hp)) (fun n => (hχ n).contDiffAt)
  obtain ⟨V, hV, hpV, N, hN⟩ := concentrated_cutoffs_eventually_zero hB b hb r hr χ hs hp
  exact ⟨N, Filter.mem_of_superset (hV.mem_nhds hpV) (fun q hq n hn => hN n hn q hq)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ComplexSourceWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact continuous complex-plane scalar with square-integrable
classical differential on an open set has its actual physical Sobolev
witness. This is used for the compact horizontal priority test. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_source_sobolev_witness
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hc : Continuous f) (hs : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ f D)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D)) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) := by
  let Ω := complexPlaneCoordinates ⁻¹' D
  let F := f ∘ complexPlaneCoordinates
  have hΩ : IsOpen Ω := hD.preimage complexPlaneCoordinates.continuous
  have hF : ContDiffOn ℝ ∞ F Ω :=
    hf.comp complexPlaneCoordinates.contDiff.contDiffOn (fun _ hp => hp)
  have hmajor : MemLp (fun p => ‖fderiv ℝ f (complexPlaneCoordinates p)‖) 2 (volume.restrict Ω) :=
    hE.norm.comp_measurePreserving (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
  have hpartial (i : Fin 2) : MemLp
      (fun p => fderiv ℝ F p (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
    have hm : AEStronglyMeasurable (fun p => fderiv ℝ F p (EuclideanSpace.single i 1))
        (volume.restrict Ω) :=
      ((hF.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const).aestronglyMeasurable hΩ.measurableSet
    apply hmajor.of_le hm
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
    have hd : DifferentiableAt ℝ f (complexPlaneCoordinates p) :=
      (hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖fderiv ℝ (f ∘ complexPlaneCoordinates) p (EuclideanSpace.single i 1)‖ ≤ _
    rw [fderiv_comp p hd complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]
    have haxis : ‖complexPlaneCoordinates (EuclideanSpace.single i 1)‖ = 1 := by
      fin_cases i
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (0 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_zero, norm_one]
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (1 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_one, Complex.norm_I]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, haxis, mul_one,
      Real.norm_eq_abs, abs_norm] using
      (fderiv ℝ f (complexPlaneCoordinates p)).le_opNorm (complexPlaneCoordinates (EuclideanSpace.single i 1))
  refine ⟨{
    memLp := ((hc.comp complexPlaneCoordinates.continuous).memLp_of_hasCompactSupport
      (hs.comp_homeomorph complexPlaneCoordinates.toHomeomorph)).restrict Ω
    weakGrad := fun p => WithLp.toLp 2 (fun i => fderiv ℝ F p (EuclideanSpace.single i 1))
    weakGrad_component_memLp := hpartial
    isWeakGrad := fun i => weakPartial_of_smooth_on hΩ (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactSourceCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact source cutoff turns local differential energy into a
compact continuous Sobolev test without making any boundary extension
assumption. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem scalar_times_cutoff_derivative_memLp
    {D : Set ℂ} {f η : ℂ → ℝ} (hc : Continuous f)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η) :
    MemLp (fun z => f z • fderiv ℝ η z) 2 (volume.restrict D) := by
  have hdη : HasCompactSupport (fderiv ℝ η) := hs.fderiv (𝕜 := ℝ)
  have hh : HasCompactSupport (f • fderiv ℝ η) := hdη.smul_left (f := f)
  exact ((hc.smul (hη.continuous_fderiv (by simp))).memLp_of_hasCompactSupport hh).restrict D

 theorem cutoff_times_local_derivative_memLp
    {D : Set ℂ} (hD : IsOpen D) {f η : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hη : ContDiff ℝ ∞ η)
    (hs : HasCompactSupport η) {R : ℝ} (hR : tsupport η ⊆ ball 0 R)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict (D ∩ ball 0 R))) :
    MemLp (fun z => η z • fderiv ℝ f z) 2 (volume.restrict D) := by
  obtain ⟨C, hC⟩ := hη.continuous.bounded_above_of_compact_support hs
  have hI : MemLp ((ball (0 : ℂ) R).indicator (fun z => ‖fderiv ℝ f z‖))
      2 (volume.restrict D) := by
    apply (memLp_indicator_iff_restrict (μ := volume.restrict D)
      (p := 2) (f := fun z => ‖fderiv ℝ f z‖) measurableSet_ball).mpr
    simpa only [Measure.restrict_restrict measurableSet_ball, inter_comm] using hE.norm
  let K := max C 0
  have hKn : 0 ≤ K := le_max_right _ _
  have hm : AEStronglyMeasurable (fun z => η z • fderiv ℝ f z) (volume.restrict D) :=
    (hη.continuous.continuousOn.smul
      (hf.continuousOn_fderiv_of_isOpen hD (by simp))).aestronglyMeasurable hD.measurableSet
  apply (hI.const_mul K).of_le hm
  filter_upwards [] with z
  by_cases hz : z ∈ ball (0 : ℂ) R
  · rw [indicator_of_mem hz]
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hKn (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((hC z).trans (le_max_left _ _)) (norm_nonneg _)
  · have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hR ht))
    simp only [hηz, zero_smul, norm_zero]
    exact norm_nonneg _

 theorem compact_source_cutoff_gradient_memLp_on
    {D : Set ℂ} (hD : IsOpen D) {f η : ℂ → ℝ}
    (hc : Continuous f) (hf : ContDiffOn ℝ ∞ f D)
    (hη : ContDiff ℝ ∞ η) (hs : HasCompactSupport η)
    {R : ℝ} (hR : tsupport η ⊆ ball 0 R)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict (D ∩ ball 0 R))) :
    MemLp (fderiv ℝ (fun z => η z*f z)) 2 (volume.restrict D) := by
  have hA := scalar_times_cutoff_derivative_memLp (D := D) hc hη hs
  have hB := cutoff_times_local_derivative_memLp hD hf hη hs hR hE
  have hsum := hA.norm.add hB.norm
  have hp : ContDiffOn ℝ ∞ (fun z => η z*f z) D := hη.contDiffOn.mul hf
  have hm : AEStronglyMeasurable (fderiv ℝ (fun z => η z*f z)) (volume.restrict D) :=
    (hp.continuousOn_fderiv_of_isOpen hD (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).aestronglyMeasurable hD.measurableSet
  apply hsum.of_le hm
  filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
  rw [fderiv_fun_mul (hη.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)
    ((hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), add_comm]
    using norm_add_le (η z • fderiv ℝ f z) (f z • fderiv ℝ η z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPriorityTest
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual priority coordinate gives a compact admissible source test.
Its classical differential on the cutoff plateau is the original one. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_priority_test (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (c : ℕ → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    {R : ℝ} (hsR : tsupport η ⊆ ball 0 R)
    (hp : Continuous (fun z : ℂ =>
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))))
    (he : MemLp (fun z : ℂ => fderiv ℝ
      (fun q : ℂ => priorityInfiniteValue (fun n => χ n q) c (M.horizontalSection (q : Sphere))) z -
      fderiv ℝ (fun q : ℂ => M.horizontalSection (q : Sphere)) z)
      2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 R))) :
    let p := fun z : ℂ => η z *
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))
    Continuous p ∧ HasCompactSupport p ∧
      ContDiffOn ℝ ∞ p {z : ℂ | (z : Sphere) ∈ G} ∧
      Nonempty (DeGiorgi.MemW1pWitness 2 (p ∘ complexPlaneCoordinates) (physicalPlaneDomain G)) := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  let X := fun z : ℂ => M.horizontalSection (z : Sphere)
  let P := fun z : ℂ => priorityInfiniteValue (fun n => χ n z) c (X z)
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hX : ContDiffOn ℝ ∞ X Dᶜᶜ := by
    simpa only [compl_compl] using M.horizontalSection_plane_smooth hG
  have hP : ContDiffOn ℝ ∞ P D := by
    simpa only [compl_compl] using priorityInfiniteValue_smooth_off_dust
      hD.isClosed_compl b hb r hr χ hχ hχs c X hX
  have hPE : MemLp (fderiv ℝ P) 2 (volume.restrict (D ∩ ball 0 R)) := by
    have hm := he.norm.add (M.horizontalSection_plane_memLp hG hinf R).norm
    have hsm : AEStronglyMeasurable (fderiv ℝ P) (volume.restrict (D ∩ ball 0 R)) :=
      ((hP.mono inter_subset_left).continuousOn_fderiv_of_isOpen (hD.inter isOpen_ball)
        (by simp)).aestronglyMeasurable (hD.inter isOpen_ball).measurableSet
    apply hm.of_le hsm
    filter_upwards [] with z
    change ‖fderiv ℝ P z‖ ≤ ‖‖fderiv ℝ P z-fderiv ℝ X z‖+‖fderiv ℝ X z‖‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ = ‖(fderiv ℝ P z-fderiv ℝ X z)+fderiv ℝ X z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hpc : Continuous (fun z => η z*P z) := hη.continuous.mul hp
  have hps : HasCompactSupport (fun z => η z*P z) := hsη.mul_right
  have hpd : ContDiffOn ℝ ∞ (fun z => η z*P z) D := hη.contDiffOn.mul hP
  have hpe := compact_source_cutoff_gradient_memLp_on hD hp hP hη hsη hsR hPE
  exact ⟨hpc, hps, hpd, complex_source_sobolev_witness hD hpc hps hpd hpe⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelPriorityPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every new pair in the actual two-coordinate append operation is null.
The support constancy is precisely the common flattened neighborhood
property used when choosing the cutoffs. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem flattened_priority_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (V : Set ℝ) (hV : MeasurableSet V) (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    (hOld : ∀ i n, ∃ a : ℝ, ∀ q ∈ {q : ℂ | (q : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ q ∈ {q : ℂ | (q : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (q : Sphere)) = a) :
    let B := {q : ℂ | (q : Sphere) ∉ G}
    let U := fun (i : Fin m) (q : ℂ) => flattenValues (O i) (sphereFromPlaneFunction (u i) (q : Sphere))
    let Q := fun q : ℂ => flattenValues V (M.heightSection H (q : Sphere))
    let P := fun q : ℂ => priorityInfiniteValue (fun n => χ n q) c (M.horizontalSection (q : Sphere))
    (∀ i, volume ((fun q => (U i q, Q q)) '' B) = 0 ∧
      volume ((fun q => (U i q, P q)) '' B) = 0) ∧
      volume ((fun q => (Q q, P q)) '' B) = 0 := by
  constructor
  · intro i
    obtain ⟨hh, hx⟩ := M.source_height_trace_pairs hsard hsch hcoarea
      hG hconn hinf hTD hu hs H hHz i
    constructor
    · exact coordinate_lipschitz_pair_null hh
        (flattenValues_lipschitz (hO i)) (flattenValues_lipschitz hV)
    · apply priority_trace_pair_null χ c _ _
        (coordinate_lipschitz_pair_null hx (flattenValues_lipschitz (hO i)) LipschitzWith.id)
      exact hOld i
  · apply priority_trace_pair_null χ c _ _
      (coordinate_lipschitz_pair_null
        (M.source_height_horizontal_pair hsard hsch hcoarea hG hconn hinf hTD H hHz)
        (flattenValues_lipschitz hV) LipschitzWith.id)
    exact hHeight

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelAppendedPairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact source priority and height coordinates preserve
every trace-pair condition when appended to the flattened old list. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_appended_trace_pairs (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (V : Set ℝ) (hV : MeasurableSet V) (χ : ℕ → ℂ → ℝ) (c : ℕ → ℝ)
    (hOld : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (z : Sphere)) = a)
    (η : ℂ → ℝ) (hη : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    (θ : EuclideanPlane → ℝ)
    (hθ : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (O i) ∘ u i)
      (M.compactPrioritySource χ c η) (M.compactHeightSource H (flattenValues V) θ)
    ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0 := by
  dsimp only
  let uf := fun i => flattenValues (O i) ∘ u i
  let p := M.compactPrioritySource χ c η
  let q := M.compactHeightSource H (flattenValues V) θ
  have heq (z : ℂ) (hz : (z : Sphere) ∉ G) :
      sphereFromPlaneFunction q (z : Sphere) = flattenValues V (M.heightSection H (z : Sphere)) := by
    simpa only [q, compactHeightSource, sphereFromPlaneFunction_coe, planeSphere,
      complexPlaneCoordinates.apply_symm_apply] using
      M.compact_height_trace hsard hsch hG hconn hinf hTD H (flattenValues V) θ hθ hz
  have hep (z : ℂ) (hz : (z : Sphere) ∉ G) :
      sphereFromPlaneFunction p (z : Sphere) = priorityInfiniteValue (fun n => χ n z) c
        (M.horizontalSection (z : Sphere)) := by
    simp only [p, compactPrioritySource, sphereFromPlaneFunction_coe,
      complexPlaneCoordinates.apply_symm_apply, hη z hz, one_mul]
  obtain ⟨hnew, hqp⟩ := M.flattened_priority_trace_pairs hsard hsch hcoarea
    hG hconn hinf hTD hu hs H hHz O hO V hV χ c hOld hHeight
  have hold (i j : Fin m) (hij : i ≠ j) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction (uf j) z)) '' Gᶜ) = 0 := by
    simpa only [uf, sphereFromPlaneFunction_flatten] using
      flattened_pair_null (hpairs i j hij) (hO i) (hO j)
  have hq (i : Fin m) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction q z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert (hnew i).1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply image_congr
    intro z hz
    simp only [uf, sphereFromPlaneFunction_flatten, heq z hz]
  have hp (i : Fin m) : volume ((fun z =>
      (sphereFromPlaneFunction (uf i) z,sphereFromPlaneFunction p z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert (hnew i).2 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply image_congr
    intro z hz
    simp only [uf, sphereFromPlaneFunction_flatten, hep z hz]
  have hqp' : volume ((fun z => (sphereFromPlaneFunction q z,sphereFromPlaneFunction p z)) '' Gᶜ) = 0 := by
    apply sphere_trace_pair_null_of_plane hinf
    convert hqp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply image_congr
    intro z hz
    simp only [heq z hz, hep z hz]
  have ha := appendScalarPair_pair_null (fun i => sphereFromPlaneFunction (uf i))
    (sphereFromPlaneFunction p) (sphereFromPlaneFunction q) hold hp hq hqp'
  intro i j hij
  convert ha i j hij using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply image_congr
  intro z _
  have hc (k : Fin (m+2)) : sphereFromPlaneFunction (appendScalarPair uf p q k) z =
      appendScalarPair (fun i => sphereFromPlaneFunction (uf i))
        (sphereFromPlaneFunction p) (sphereFromPlaneFunction q) k z := by
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun _ => rfl) l
  exact congrArg₂ Prod.mk (hc i) (hc j)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelAppendedTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite appended list consists of actual continuous compact tests
with local Sobolev witnesses and all pair-null relations. Its ingredients
are the constructed flattenings, priority cutoffs and descended height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_appended_tests (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ p = 0)
    (O : Fin m → Set ℝ) (hO : ∀ i, MeasurableSet (O i))
    (WO : ∀ i, DeGiorgi.MemW1pWitness 2 (flattenValues (O i) ∘ u i) (physicalPlaneDomain G))
    (V : Set ℝ) (hV : MeasurableSet V) (A : ℝ)
    (WV : DeGiorgi.MemW1pWitness 2 (flattenValues V ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A))
    (b : ℕ → ℂ) (hb : ∀ n, (b n : Sphere) ∉ G)
    (c : ℕ → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → ℂ → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hχs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hOld : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues (O i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a)
    (hHeight : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (χ n),
      flattenValues V (M.heightSection H (z : Sphere)) = a)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1)
    {L : ℝ} (hsL : tsupport η ⊆ ball 0 L)
    (hp : Continuous (fun z : ℂ =>
      priorityInfiniteValue (fun n => χ n z) c (M.horizontalSection (z : Sphere))))
    (he : MemLp (fun z : ℂ => fderiv ℝ
      (fun w : ℂ => priorityInfiniteValue (fun n => χ n w) c (M.horizontalSection (w : Sphere))) z -
      fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
      2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L)))
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A)
    (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (O i) ∘ u i)
      (M.compactPrioritySource χ c η) (M.compactHeightSource H (flattenValues V) θ)
    (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
      Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
      (∀ i j, i ≠ j → volume ((fun p =>
        (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0) := by
  obtain ⟨hpc, hps, _, WP⟩ := M.compact_priority_test hG hinf b hb c r hr χ hχ hχs
    η hη hsη hsL hp he
  obtain ⟨hqc, hqs, WQ⟩ := M.compact_flattened_height_pullback hsard hsch
    hG hconn hinf hTD H hHz V hV A WV θ hθ hsθ hθA hθF
  obtain ⟨WP⟩ := WP
  obtain ⟨WQ⟩ := WQ
  refine ⟨?_, ?_, ?_, M.compact_appended_trace_pairs hsard hsch hcoarea
    hG hconn hinf hTD hu hs hpairs H hHz O hO V hV χ c hOld hHeight η hηB θ hθF⟩
  · intro i
    refine Fin.cases hqc (fun j => ?_) i
    refine Fin.cases (hpc.comp complexPlaneCoordinates.continuous) (fun k => ?_) j
    exact (flattenValues_lipschitz (hO k)).continuous.comp (hu k)
  · intro i
    refine Fin.cases hqs (fun j => ?_) i
    refine Fin.cases (hps.comp_homeomorph complexPlaneCoordinates.toHomeomorph) (fun k => ?_) j
    exact (hs k).comp_left (flattenValues_zero (O k))
  · exact ⟨Fin.cases WQ (Fin.cases WP WO)⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ModelSelectedTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The simultaneous selection is an admissible finite appended list,
ready for the proved scalar circle-model construction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.compact_tests_oai (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1) (hsL : tsupport η ⊆ ball 0 L)
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A)
    (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (S.oldValues i) ∘ u i)
      (M.compactPrioritySource S.cutoff S.value η)
      (M.compactHeightSource H (flattenValues S.heightValues) θ)
    (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
      Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
      (∀ i j, i ≠ j → volume ((fun p =>
        (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0) :=
  M.compact_appended_tests hsard hsch hcoarea hG hconn hinf hTD hu hs hpairs H hHz
    S.oldValues (fun i => (S.old_open i).measurableSet) S.oldWitness
    S.heightValues S.height_open.measurableSet A S.heightWitness
    S.center S.center_outside S.value S.radius S.radius_tendsto S.cutoff S.cutoff_smooth S.cutoff_support
    S.old_constant S.height_constant η hη hsη hηB hsL S.priority_continuous S.priority_error_memLp
    θ hθ hsθ hθA hθF

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests_oai := @OAI.CircleDomainRigidity.CompactScalarModel.FlattenedSourceSelection.compact_tests_oai
