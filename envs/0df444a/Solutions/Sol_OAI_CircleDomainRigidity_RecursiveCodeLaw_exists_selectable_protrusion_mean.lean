-- Prove2me | solution 1 for OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:00:47.228002+00:00
-- url     : https://prove2.me/submissions/bcd4669a-d13d-4eba-a903-87bca9ae6841

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010
import Theorems.Thm_OAI_CircleDomainRigidity_RecursiveCodeLaw_eventually_protrusion_mean
import Theorems.Thm_OAI_CircleDomainRigidity_SelectedLevelPresentation_generic_levels

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DustCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small disjoint neighborhoods of compact dust

A compact totally disconnected subset of a metric space admits finite
open covers with pairwise disjoint closures of arbitrarily small diameter.
-/

open Set Metric TopologicalSpace Filter Function
open scoped Topology

namespace CircleDomainRigidity

theorem exists_small_disjoint_open_cover_of_compact_dust
    {X : Type*} [MetricSpace X] {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (U : Fin n → Set X),
      (∀ i, IsOpen (U i)) ∧ B ⊆ ⋃ i, U i ∧
      Pairwise (Disjoint on fun i => closure (U i)) ∧
      ∀ i, diam (closure (U i)) < ε := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : TotallyDisconnectedSpace B := totallyDisconnectedSpace_subtype_iff.mpr hTD
  have hcover : IsOpenCover (fun b : B => (⟨ball b (ε / 4), isOpen_ball⟩ : Opens B)) := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro b
    exact mem_iUnion.mpr ⟨b, mem_ball_self (by positivity)⟩
  obtain ⟨n, C, hC, hCov, hDisj⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  let A : Fin n → Set X := fun i => Subtype.val '' (C i : Set B)
  have hAc (i) : IsCompact (A i) := (C i).isClosed.isCompact.image continuous_subtype_val
  have hAd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have heq : v = u := Subtype.ext huv
    subst v
    exact Set.disjoint_left.mp (Clopens.coe_disjoint.mpr (hDisj hij)) hu hv
  have hAn : Pairwise (Disjoint on fun i => 𝓝ˢ (A i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hAc i).isClosed (hAc j).isClosed (hAd hij)
  obtain ⟨V, hV, hVd⟩ := hAn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (A i))
  have hsmall (i : Fin n) : ∃ b : B, A i ⊆ ball (b : X) (ε / 4) := by
    obtain ⟨b, hb⟩ := (hC i).2
    refine ⟨b, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    exact hb hu
  choose b hb using hsmall
  have hshrink (i : Fin n) : ∃ U : Set X,
      IsOpen U ∧ A i ⊆ U ∧ closure U ⊆ V i ∩ ball (b i : X) (ε / 4) := by
    apply (hAc i).exists_isOpen_closure_subset
    exact ((hV i).1.inter isOpen_ball).mem_nhdsSet.mpr
      (subset_inter (hV i).2 (hb i))
  choose U hUo hAU hUV using hshrink
  refine ⟨n, U, hUo, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCov (mem_univ (⟨x, hx⟩ : B)))
    exact mem_iUnion.mpr ⟨i, hAU i ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro i j hij
    exact (hVd hij).mono (fun _ hx => (hUV i hx).1) (fun _ hx => (hUV j hx).1)
  · intro i
    have hdiam : diam (closure (U i)) ≤ 2 * (ε / 4) :=
      diam_le_of_subset_closedBall (by positivity)
        (fun _ hx => ball_subset_closedBall ((hUV i hx).2))
    linarith

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
-- module Solutions.Q146_CD.CircleDomains_Selection_FinitelySuslinian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

/-- The finite bound is inherited by metric subspaces, with the same
bound on cardinalities. -/
theorem HasFiniteLargeContinuumBound.subtype {X : Type*} [MetricSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (K : Set X) :
    HasFiniteLargeContinuumBound K := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := hbound ε hε
  refine ⟨N, ?_⟩
  intro S hS hdisj
  let e : Set K → Set X := Set.image Subtype.val
  have he : Function.Injective e := Subtype.val_injective.image_injective
  have hiso : Isometry ((↑) : K → X) := fun _ _ => rfl
  have hle := hN (S.image e) (by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨hc, hconn, hdiam⟩ := hS D hD
    refine ⟨hc.image continuous_subtype_val,
      hconn.image Subtype.val continuous_subtype_val.continuousOn, ?_⟩
    simpa only [e, hiso.diam_image] using hdiam) (by
    intro C hC D hD hne
    obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.mp hD
    exact (Set.disjoint_image_iff Subtype.val_injective).mpr
      (hdisj C' hC' D' hD' (fun h => hne (congrArg e h))))
  rwa [Finset.card_image_of_injective S he] at hle

/-- In particular every compact connected subcontinuum is locally
connected under the ambient finite-continuum bound. -/
theorem locallyConnected_subcontinuum_of_finite_large_continuum_bound
    {X : Type*} [MetricSpace X] (hbound : HasFiniteLargeContinuumBound X)
    {K : Set X} (hK : IsCompact K) (hconn : IsConnected K) :
    LocallyConnectedSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : PreconnectedSpace K := Subtype.preconnectedSpace hconn.isPreconnected
  exact locallyConnectedSpace_of_finite_large_continuum_bound (hbound.subtype K)

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

/-- A compact continuum through the center and exiting a closed ball
pays at least the radius in physical Hausdorff length, provided the ball
lies in the physical domain. No local connectedness is assumed. -/
theorem radius_le_hausdorffMeasure_inter_of_exits_closedBall
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {C G : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    {p : X} (hp : p ∈ C) {r : ℝ} (hr : 0 < r)
    (hball : closedBall p r ⊆ G) (hexit : ∃ q ∈ C, r < dist q p) :
    ENNReal.ofReal r ≤ (μH[1] : Measure X) (C ∩ G) := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  let pc : C := ⟨p, hp⟩
  let F : Set C := Subtype.val ⁻¹' closedBall p r
  have hFclosed : IsClosed F := isClosed_closedBall.preimage continuous_subtype_val
  have hpF : pc ∈ F := by
    change dist p p ≤ r
    simpa using hr.le
  have hproper : F ≠ univ := by
    obtain ⟨q, hq, hqout⟩ := hexit
    intro heq
    have hqF : (⟨q, hq⟩ : C) ∈ F := by rw [heq]; trivial
    exact (not_le.mpr hqout) hqF
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hFclosed hproper hpF
  have hzboundary : z.val ∈ frontier (closedBall p r) :=
    continuous_subtype_val.frontier_preimage_subset _ hzfront
  have hzdist : dist z.val p = r := frontier_closedBall_subset_sphere hzboundary
  let K := connectedComponentIn F pc
  let D : Set X := Subtype.val '' K
  have hDconn : IsPreconnected D :=
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
  have hpD : p ∈ D := ⟨pc, mem_connectedComponentIn hpF, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hDsub : D ⊆ C ∩ G := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.property, hball (connectedComponentIn_subset F pc hw)⟩
  calc
    ENNReal.ofReal r = ENNReal.ofReal (dist z.val p) := congrArg _ hzdist.symm
    _ ≤ (μH[1] : Measure X) D :=
      dist_le_hausdorffMeasure_one_of_preconnected hDconn hpD hzD
    _ ≤ (μH[1] : Measure X) (C ∩ G) := measure_mono hDsub

/-- The physical length on `G`, pushed through a monotone quotient,
gives the finite bound on large quotient continua. The remaining
geometric hypothesis supplies a uniformly sized physical ball crossed
by each sufficiently large quotient continuum. -/
theorem finite_large_continuum_bound_of_quotient_length
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y}
    (hlength : (μH[1] : Measure Y) G < ∞)
    (hcross : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
        ∃ p ∈ π ⁻¹' C, closedBall p r ⊆ G ∧ ∃ q ∈ π ⁻¹' C, r < dist q p) :
    HasFiniteLargeContinuumBound X := by
  let ν : Measure Y := (μH[1] : Measure Y).restrict G
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hlength.ne
  let μ : Measure X := ν.map π
  apply finite_large_continuum_bound_of_measure μ
  intro ε hε
  obtain ⟨r, hr, hcrossr⟩ := hcross ε hε
  refine ⟨r, hr, ?_⟩
  intro C hcompact hconn hdiam
  obtain ⟨p, hp, hball, hexit⟩ := hcrossr C hcompact hconn hdiam
  have hCmeas : MeasurableSet C := hcompact.isClosed.measurableSet
  have hprecompact : IsCompact (π ⁻¹' C) := (hcompact.isClosed.preimage hπ).isCompact
  have hpreconn : IsConnected (π ⁻¹' C) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed hfiber
      (hπ.isClosedMap.isQuotientMap hπ hsurj).isCoinducing hcompact.isClosed hconn
  have hpay := radius_le_hausdorffMeasure_inter_of_exits_closedBall
    hprecompact hpreconn hp hr hball hexit
  have hμC : μ C = (μH[1] : Measure Y) ((π ⁻¹' C) ∩ G) := by
    change ν.map π C = _
    rw [Measure.map_apply hπ.measurable hCmeas]
    exact Measure.restrict_apply (hCmeas.preimage hπ.measurable)
  have hpay' : ENNReal.ofReal r ≤ μ C := hμC.symm ▸ hpay
  have hreal := ENNReal.toReal_mono (measure_ne_top μ C) hpay'
  simpa only [ENNReal.toReal_ofReal hr.le, measureReal_def] using hreal

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_CoreCrossing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform crossing from a compact physical core

This supplies the geometric input to the length-payment argument in
the generic-level-continua lemma. A compact core inside the physical
domain has a uniform ball neighborhood there. Uniform continuity of
the quotient map makes these balls too small to contain a large
quotient continuum.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- A connected continuum covered off a core by disjoint open sets of
small diameter must meet that core. In the application the ambient
compact metric space is the level union itself. -/
theorem continuum_meets_core_of_small_open_cover
    {X ι : Type*} [MetricSpace X] [CompactSpace X]
    {F C : Set X} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (Disjoint on U)) (hcover : Fᶜ ⊆ ⋃ i, U i)
    {ε : ℝ} (hsmall : ∀ i, diam (U i) < ε)
    (hconn : IsConnected C) (hdiam : ε ≤ diam C) : (C ∩ F).Nonempty := by
  classical
  by_contra hmeet
  have hCU : C ⊆ ⋃ i, U i := by
    intro x hx
    apply hcover
    intro hxF
    exact hmeet ⟨x, hx, hxF⟩
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hCU hx)
  let V : Set X := ⋃ j : {j : ι // j ≠ i}, U j.val
  have hVopen : IsOpen V := isOpen_iUnion (fun j => hopen j.val)
  have hiV : Disjoint (U i) V := by
    apply disjoint_iUnion_right.mpr
    intro j
    exact hdisj j.property.symm
  have hunion : C ⊆ U i ∪ V := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hCU hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hCi := hconn.isPreconnected.subset_left_of_subset_union
    (hopen i) hVopen hiV hunion ⟨x, hx, hi⟩
  have hd : diam C ≤ diam (U i) :=
    diam_mono hCi (isCompact_univ.isBounded.subset (subset_univ _))
  exact (not_lt_of_ge (hdiam.trans hd)) (hsmall i)

/-- A compact physical core meeting every sufficiently large quotient
continuum supplies uniformly sized physical balls that those continua
must exit. -/
theorem uniform_ball_crossing_of_compact_core
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    {G K : Set Y} (hG : IsOpen G) (hK : IsCompact K) (hKG : K ⊆ G)
    {ε : ℝ} (hε : 0 < ε)
    (hcore : ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
      (C ∩ π '' K).Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∀ C : Set X,
      IsCompact C → IsConnected C → ε ≤ diam C →
      ∃ p ∈ π ⁻¹' C, closedBall p r ⊆ G ∧ ∃ q ∈ π ⁻¹' C, r < dist q p := by
  obtain ⟨ρ, hρ, hthick⟩ := hK.exists_cthickening_subset_open hG hKG
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hπ) (ε / 3) (by positivity)
  let r := min ρ (δ / 2)
  have hr : 0 < r := lt_min hρ (half_pos hδ)
  refine ⟨r, hr, ?_⟩
  intro C hcompact hconn hdiam
  obtain ⟨x, hxC, p, hpK, hpx⟩ := hcore C hcompact hconn hdiam
  have hpC : p ∈ π ⁻¹' C := by simpa only [mem_preimage, hpx] using hxC
  refine ⟨p, hpC, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (min_le_left ρ (δ / 2))).trans
      ((closedBall_subset_cthickening hpK ρ).trans hthick)
  · by_contra hno
    push Not at hno
    have hCball : C ⊆ closedBall (π p) (ε / 3) := by
      intro y hy
      obtain ⟨q, hq⟩ := hsurj y
      have hqC : q ∈ π ⁻¹' C := by simpa only [mem_preimage, hq] using hy
      have hqp : dist q p < δ :=
        (hno q hqC).trans_lt ((min_le_right ρ (δ / 2)).trans_lt (half_lt_self hδ))
      have hdist := hsmall hqp
      change dist y (π p) ≤ ε / 3
      exact hq ▸ hdist.le
    have hd := diam_le_of_subset_closedBall (by positivity : 0 ≤ ε / 3) hCball
    linarith

/-- Finite physical level length and arbitrarily fine compact cores give
the finite large-continuum bound in the quotient. The core-intersection
hypothesis is explicit; the radius choice, ball crossing, Hausdorff
payment, and cardinal estimate are all derived. -/
theorem finite_large_continuum_bound_of_compact_cores
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    (hlength : (μH[1] : Measure Y) G < ∞)
    (hcores : ∀ ε : ℝ, 0 < ε → ∃ K : Set Y,
      IsCompact K ∧ K ⊆ G ∧
      ∀ C : Set X, IsCompact C → IsConnected C → ε ≤ diam C →
        (C ∩ π '' K).Nonempty) : HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_quotient_length π hπ hsurj hfiber hlength
  intro ε hε
  obtain ⟨K, hK, hKG, hcore⟩ := hcores ε hε
  exact uniform_ball_crossing_of_compact_core π hπ hsurj hG hK hKG hε hcore

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GenericLevelTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topology of finite-length level unions

The compact spaces here are a quotient level union and its physical
preimage, with the induced metrics. Thus finite Hausdorff length on
`G` is finite physical level length, not finite length of a planar open
domain. Compact totally disconnected quotient dust supplies the small
disjoint covers and hence compact physical cores. All counting and
local connectedness conclusions are then proved.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- Finite physical length and compact totally disconnected quotient
dust imply the finite bound on disjoint large subcontinua. -/
theorem finite_large_continuum_bound_of_compact_quotient_dust
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Function.Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) {G : Set Y} (hG : IsOpen G)
    {B : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hdust : π '' Gᶜ ⊆ B) (hlength : (μH[1] : Measure Y) G < ∞) :
    HasFiniteLargeContinuumBound X := by
  apply finite_large_continuum_bound_of_compact_cores π hπ hsurj hfiber hG hlength
  intro ε hε
  obtain ⟨n, U, hopen, hcoverB, hdisj, hsmall⟩ :=
    exists_small_disjoint_open_cover_of_compact_dust hB hTD hε
  let K : Set Y := π ⁻¹' (⋃ i, U i)ᶜ
  have hK : IsCompact K := ((isOpen_iUnion hopen).isClosed_compl.preimage hπ).isCompact
  have hKG : K ⊆ G := by
    intro p hp
    by_contra hpG
    have hpB : π p ∈ B := hdust ⟨p, hpG, rfl⟩
    exact hp (hcoverB hpB)
  have hcoreCover : (π '' K)ᶜ ⊆ ⋃ i, U i := by
    intro x hx
    by_contra hxU
    obtain ⟨p, rfl⟩ := hsurj x
    exact hx ⟨p, hxU, rfl⟩
  have hUdisj : Pairwise (Disjoint on U) := by
    intro i j hij
    exact (hdisj hij).mono subset_closure subset_closure
  have hUsmall (i : Fin n) : diam (U i) < ε := by
    simpa only [diam_closure] using hsmall i
  refine ⟨K, hK, hKG, ?_⟩
  intro C _ hconn hdiam
  exact continuum_meets_core_of_small_open_cover U hopen hUdisj hcoreCover hUsmall hconn hdiam

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LevelQuotient
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting the quotient to a compact level union

The original quotient acts on the whole compact physical space. For a
compact level union `H`, restrict it to `π ⁻¹' H → H`. Connected fibers
remain connected, omitted points still map into compact totally
disconnected dust, and the induced-metric Hausdorff length is exactly
the physical length of `(π ⁻¹' H) ∩ G`.
-/

open Set Metric MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity

theorem continuous_levelQuotientMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hπ : Continuous π) (H : Set X) :
    Continuous (levelQuotientMap π H) :=
  (hπ.comp continuous_subtype_val).subtype_mk _

theorem surjective_levelQuotientMap {X Y : Type*} {π : Y → X}
    (hsurj : Surjective π) (H : Set X) : Surjective (levelQuotientMap π H) := by
  intro x
  obtain ⟨y, hy⟩ := hsurj x.val
  have hyH : y ∈ π ⁻¹' H := by simpa only [mem_preimage, hy] using x.property
  exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩

theorem connected_fibers_levelQuotientMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {π : Y → X} (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x})) (H : Set X) (x : H) :
    IsConnected (levelQuotientMap π H ⁻¹' {x}) := by
  have himage : (Subtype.val : (π ⁻¹' H) → Y) '' (levelQuotientMap π H ⁻¹' {x}) =
      π ⁻¹' {x.val} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val hz
    · intro hy
      have hyH : y ∈ π ⁻¹' H := by
        change π y ∈ H
        simpa only [show π y = x.val from hy] using x.property
      exact ⟨⟨y, hyH⟩, Subtype.ext hy, rfl⟩
  refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
  · obtain ⟨y, hy⟩ := surjective_levelQuotientMap hsurj H x
    exact ⟨y, hy⟩
  · rw [himage]
    exact (hfiber x.val).isPreconnected

/-- The finite-continuum bound on an actual compact quotient level set,
from its physical level length. -/
theorem finite_large_continuum_bound_on_level
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H)
    (hlength : (μH[1] : Measure Y) ((π ⁻¹' H) ∩ G) < ∞) :
    HasFiniteLargeContinuumBound H := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hpreclosed : IsClosed (π ⁻¹' H) := hH.isClosed.preimage hπ
  let : CompactSpace (π ⁻¹' H) := isCompact_iff_compactSpace.mp hpreclosed.isCompact
  let GH : Set (π ⁻¹' H) := Subtype.val ⁻¹' G
  let BH : Set H := Subtype.val ⁻¹' B
  have hGH : IsOpen GH := hG.preimage continuous_subtype_val
  have hBH : IsCompact BH := (hB.isClosed.preimage continuous_subtype_val).isCompact
  have hTDH : IsTotallyDisconnected BH := by
    apply isTotallyDisconnected_of_image continuous_subtype_val.continuousOn
      Subtype.val_injective
    intro C hC hconn
    apply hTD C ?_ hconn
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hC hz
    exact hx
  have hdustH : levelQuotientMap π H '' GHᶜ ⊆ BH := by
    rintro _ ⟨y, hy, rfl⟩
    exact hdust ⟨y.val, hy, rfl⟩
  have hiso : Isometry (Subtype.val : (π ⁻¹' H) → Y) := fun _ _ => rfl
  have hlengthH : (μH[1] : Measure (π ⁻¹' H)) GH < ∞ := by
    rw [← hiso.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1))]
    simpa only [GH, Subtype.image_preimage_coe] using hlength
  exact finite_large_continuum_bound_of_compact_quotient_dust
    (levelQuotientMap π H) (continuous_levelQuotientMap hπ H)
    (surjective_levelQuotientMap hsurj H) (connected_fibers_levelQuotientMap hsurj hfiber H)
    hGH hBH hTDH hdustH hlengthH

/-- Countability and local connectedness for the actual compact level
union, without replacing the whole physical space by an unspecified
finite-length ambient space. -/
theorem level_topology_of_finite_physical_length
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H)
    (hlength : (μH[1] : Measure Y) ((π ⁻¹' H) ∩ G) < ∞) :
    HasFiniteLargeContinuumBound H ∧
      {C : Set H | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}.Countable ∧
      ∀ C : Set H, IsCompact C → IsConnected C → LocallyConnectedSpace C := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hbound := finite_large_continuum_bound_on_level π hπ hsurj hfiber
    hG hB hTD hdust hH hlength
  exact ⟨hbound, countable_nontrivial_connectedComponents hbound,
    fun _ hcompact hconn =>
      locallyConnected_subcontinuum_of_finite_large_continuum_bound hbound hcompact hconn⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConfigurationNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Testing all sizes and reciprocal separation scales is sufficient to control
the full square norm of the point-hit probabilities. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_reciprocal_separation {X I : Type*} [MetricSpace X] [Finite I]
    (x : I → X) (hx : Injective x) :
    ∃ m : ℕ, ∀ i j, i ≠ j → 1 / ((m : ℝ) + 1) ≤ dist (x i) (x j) := by
  obtain ⟨c, hc, hsep⟩ := (Set.finite_range x).relatively_discrete
  obtain ⟨a, ha, hac⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt ha0
  refine ⟨m, fun i j hij => hm.le.trans ?_⟩
  have hd := hac.le.trans (hsep (x i) (mem_range_self i) (x j) (mem_range_self j)
    (fun h => hij (hx h)))
  rw [edist_dist] at hd
  have hdreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  simpa only [ENNReal.coe_toReal, ENNReal.toReal_ofReal dist_nonneg] using hdreal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite visit witnesses have Borel incidence. The resulting extended count
records visits at distinct parameter times, including both endpoints. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem isClosed_separatedTimeSet (n : ℕ) (r : ℝ) : IsClosed (separatedTimeSet n r) := by
  simp only [separatedTimeSet, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)

instance instCompactSpaceElemForallFinRealPathTimeSeparatedTimes (n : ℕ) (r : ℝ) : CompactSpace (SeparatedTimes n r) :=
  isCompact_iff_compactSpace.mp (isClosed_separatedTimeSet n r).isCompact

theorem isClosed_separatedVisitSet {X : Type*} [MetricSpace X] (n : ℕ) (r : ℝ) :
    IsClosed (separatedVisitSet (X := X) n r) := by
  let H : Set ((C(PathTime, X) × X) × SeparatedTimes n r) :=
    {q | ∀ i, q.1.1 (q.2.val i) = q.1.2}
  have hH : IsClosed H := by
    simp only [H, ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_eq
    · exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    · exact continuous_snd.comp continuous_fst
  have heq : Prod.fst '' H = separatedVisitSet (X := X) n r := by
    ext q
    constructor
    · rintro ⟨⟨p, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(q, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

theorem visitAtLeastSet_eq_iUnion {X : Type*} [MetricSpace X] (n : ℕ) :
    visitAtLeastSet (X := X) n =
      ⋃ m : ℕ, separatedVisitSet n (1 / ((m : ℝ) + 1)) := by
  ext q
  constructor
  · rintro ⟨t, ht, heq⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation t ht
    exact mem_iUnion.mpr ⟨m, ⟨⟨t, hm⟩, heq⟩⟩
  · intro h
    obtain ⟨m, t, ht⟩ := mem_iUnion.mp h
    refine ⟨t.val, ?_, ht⟩
    intro i j hij
    by_contra hne
    have hd := t.property i j hne
    rw [hij, dist_self] at hd
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_visitAtLeastSet (n : ℕ) :
    MeasurableSet (visitAtLeastSet (X := X) n) := by
  rw [visitAtLeastSet_eq_iUnion]
  exact MeasurableSet.iUnion fun m => (isClosed_separatedVisitSet n (1 / ((m : ℝ) + 1))).measurableSet

theorem measurable_visitCount : Measurable (fun q : C(PathTime, X) × X => visitCount q.1 q.2) := by
  classical
  unfold visitCount
  apply Measurable.iSup
  intro n
  exact measurable_const.piecewise (measurableSet_visitAtLeastSet (X := X) n) measurable_const

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidateBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative outputs of countable modulus extraction are members of
one fixed candidate family, independent of the prescribed countable set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanVisitCount_codePathLaw_eq_integral (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) (s : S) :
    meanVisitCount (codePathLaw d P) (a s) =
      ∫⁻ Γ, codeVisitWeight d a s Γ ∂(P : Measure (BasePathCode d)) := by
  have hv : Measurable (fun γ : C(PathTime, X) => visitCount γ (a s)) :=
    measurable_visitCount.comp (measurable_id.prodMk measurable_const)
  unfold meanVisitCount codePathLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hv (measurable_codePath d)]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawCandidateConsequences
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unpack the fused candidate's quantitative estimates and slot laws. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y S : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem countableSquareLawBounds_visit_norm (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (a : S → X) {C : ℝ≥0∞}
    (h : CountableSquareLawBounds (codeVisitWeight d a) (C ^ 2) P) :
    countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (a s)) ≤ C := by
  have hs : (∑' s, meanVisitCount (codePathLaw d P) (a s) ^ 2) ≤ C ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    simpa only [meanVisitCount_codePathLaw_eq_integral] using h F
  calc
    _ ≤ (C ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hs (by norm_num)
    _ = C := by rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableLawRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction of the full mean-visit bound to any injectively indexed
subfamily of the prescribed marks. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem countingSquareNorm_comp_injective {A B : Type*} (v : B → ℝ≥0∞)
    (e : A → B) (he : Injective e) : countingSquareNorm (v ∘ e) ≤ countingSquareNorm v := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_comp_le_tsum_of_injective he (fun b => v b ^ 2)

theorem countingSquareNorm_restrict_range {X A B : Type*} (v : X → ℝ≥0∞)
    (a : A → X) (b : B → X) (ha : Injective a) (hab : range a ⊆ range b) :
    countingSquareNorm (v ∘ a) ≤ countingSquareNorm (v ∘ b) := by
  classical
  choose e he using fun s => hab (mem_range_self s)
  have hinj : Injective e := by
    intro s t h
    apply ha
    rw [← he s, ← he t, h]
  simpa only [Function.comp_def, he] using
    countingSquareNorm_comp_injective (v ∘ b) e hinj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DustPriorBudgets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The candidate's prescribed-mark budget supplies exactly the dust
visit norms used by the prior-contact argument. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem candidate_visit_norm_on_marks (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (M T : Set X) (hTM : T ⊆ M)
    {C : ℝ≥0∞}
    (hb : CountableSquareLawBounds (codeVisitWeight d (fun x : M => x.val)) (C ^ 2) P) :
    countingSquareNorm (fun x : T => meanVisitCount (codePathLaw d P) x.val) ≤ C := by
  have hsub : range (fun x : T => x.val) ⊆ range (fun x : M => x.val) := by
    rintro x ⟨t, rfl⟩
    exact ⟨⟨t.val, hTM t.property⟩, rfl⟩
  exact (countingSquareNorm_restrict_range (meanVisitCount (codePathLaw d P))
    (fun x : T => x.val) (fun x : M => x.val) Subtype.val_injective hsub).trans
      (countableSquareLawBounds_visit_norm d P (fun x : M => x.val) hb)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodizedLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Periodizing scalar coarea lengths

A scalar coarea estimate controls the integral of the physical length
of real level sets. Integer translates of `[0,1)` partition the real
line, so the sum of these lengths over all lifts of a mod-one level
has the same integral on `[0,1)`. Countable subadditivity then gives
finite physical length for almost every mod-one level.
-/

open Set MeasureTheory Metric Function
open scoped ENNReal

namespace CircleDomainRigidity

/-- The actual mod-one fiber of any real coordinate is the countable
union of its integer-translated scalar fibers. -/
theorem unitAddCircle_level_eq_iUnion_integer_levels {Z : Type*} (f : Z → ℝ) (t : ℝ) :
    {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, {x | f x = t + (k : ℝ)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, unitAddCircle_eq_iff_exists_int]

theorem unitAddCircle_level_inter_eq_iUnion_integer_levels
    {Z : Type*} (f : Z → ℝ) (D : Set Z) (t : ℝ) :
    D ∩ {x | (f x : UnitAddCircle) = (t : UnitAddCircle)} =
      ⋃ k : ℤ, D ∩ {x | f x = t + (k : ℝ)} := by
  rw [unitAddCircle_level_eq_iUnion_integer_levels, inter_iUnion]

private theorem iUnion_integer_Ico : (⋃ k : ℤ, Ico (k : ℝ) ((k : ℝ) + 1)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

private theorem pairwise_disjoint_integer_Ico :
    Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) ((k : ℝ) + 1)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : i + 1 ≤ j := by omega
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hstep
    linarith
  · have hstep : j + 1 ≤ i := by omega
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hstep
    linarith

/-- Tonelli and the integer translates of a unit interval give the exact
periodized coarea integral. -/
theorem lintegral_periodizedLevelLength (L : ℝ → ℝ≥0∞) (hL : Measurable L) :
    ∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t = ∫⁻ t, L t := by
  unfold periodizedLevelLength
  have hm (k : ℤ) : AEMeasurable (fun t : ℝ => L (t + (k : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    (hL.comp (measurable_id.add_const (k : ℝ))).aemeasurable
  rw [lintegral_tsum hm]
  have hshift (k : ℤ) :
      ∫⁻ t in Ico (0 : ℝ) 1, L (t + (k : ℝ)) =
        ∫⁻ t in Ico (k : ℝ) ((k : ℝ) + 1), L t := by
    have h := (measurePreserving_add_right volume (k : ℝ)).setLIntegral_comp_emb
      (Homeomorph.addRight (k : ℝ)).isClosedEmbedding.measurableEmbedding L (Ico 0 1)
    simpa only [image_add_const_Ico, zero_add, add_comm (1 : ℝ) (k : ℝ)] using h
  simp_rw [hshift]
  rw [← lintegral_iUnion (fun _ : ℤ => measurableSet_Ico) pairwise_disjoint_integer_Ico,
    iUnion_integer_Ico, Measure.restrict_univ]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

/-- Countable additivity on the disjoint integer lifts is the exact
weighted circle-fiber identity. -/
theorem weightedCircleLevelLength_eq_periodized {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedCircleLevelLength D f q t =
      periodizedLevelLength (weightedScalarLevelLength D f q) t := by
  unfold weightedCircleLevelLength periodizedLevelLength weightedScalarLevelLength
  rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  apply lintegral_iUnion (fun k : ℤ => measurableSet_scalar_level hD hf (t + (k : ℝ)))
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨_, hzi⟩ ⟨_, hzj⟩
  change f z = t + (i : ℝ) at hzi
  change f z = t + (j : ℝ) at hzj
  apply hij
  exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)

theorem lintegral_periodizedLevelLength_of_aemeasurable
    (L : ℝ → ℝ≥0∞) (hL : AEMeasurable L volume) :
    (∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t) = ∫⁻ t, L t := by
  have htranslate (k : ℤ) :
      ∀ᵐ t ∂volume, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae hL.ae_eq_mk
  have heq : periodizedLevelLength L =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      periodizedLevelLength (hL.mk L) := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr htranslate)] with t ht
    exact tsum_congr ht
  rw [lintegral_congr_ae heq, lintegral_periodizedLevelLength _ hL.measurable_mk,
    ← lintegral_congr_ae hL.ae_eq_mk]

/-- The weighted circle-valued coarea formula follows from the real
one, including the measurability needed for further integration. -/
theorem weighted_circle_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞)
    (hcoarea : WeightedScalarCoareaIdentity D f q) :
    AEMeasurable (weightedCircleLevelLength D f q)
        (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻ t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
  have heq : weightedCircleLevelLength D f q =
      periodizedLevelLength (weightedScalarLevelLength D f q) :=
    funext (weightedCircleLevelLength_eq_periodized hD hf q)
  rw [heq]
  constructor
  · apply AEMeasurable.restrict
    exact AEMeasurable.tsum (fun k : ℤ => hcoarea.1.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving)
  · rw [lintegral_periodizedLevelLength_of_aemeasurable _ hcoarea.1, hcoarea.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExtendedWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted level estimate allows extended nonnegative densities.
Finite squared energy suffices; no pointwise finiteness is imposed. -/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have h : (a : ℝ) * (b : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ)), sq_nonneg (a : ℝ), sq_nonneg (b : ℝ)]
  exact_mod_cast h

theorem weighted_circle_coarea_extended_finite_energy
    (hcoarea : WeightedPlanarScalarCoarea) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    AEMeasurable (weightedCircleLevelLength D f q) (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        (∫⁻z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ∧
      ∀ᵐt ∂volume.restrict (Ico (0 : ℝ) 1), weightedCircleLevelLength D f q t < ∞ := by
  obtain ⟨hmeas, heq⟩ := weighted_circle_coarea hD hf.continuousOn q (hcoarea D hD f hf q hq)
  have hfinite : (∫⁻t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) < ∞ := by
    rw [heq]
    calc
      _ ≤ ∫⁻z in D, (q z ^ 2 + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) := by
        apply lintegral_mono
        intro z
        simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using
          ennreal_mul_le_sq_add_sq (q z) (ENNReal.ofReal ‖fderiv ℝ f z‖)
      _ = (∫⁻z in D, q z ^ 2) + ∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) :=
        lintegral_add_left (hq.pow_const 2) _
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩
  exact ⟨hmeas, heq, ae_lt_top' hmeas hfinite.ne⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteLevelPayments
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite physical and atomic payments pass to independent finite level
tuples, including tuples with repeated labels. -/

open Set Function MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_finite_lintegral_level_union
    {X T J Λ : Type*} [MeasurableSpace X] [MeasurableSpace T] [Fintype J]
    (μ : Measure X) (ν : Measure T) [SigmaFinite ν]
    (A : Λ → T → Set X) (g : X → ℝ≥0∞) (labels : J → Λ)
    (hfinite : ∀l, ∀ᵐt ∂ν, (∫⁻x in A l t, g x ∂μ) < ∞) :
    ∀ᵐθ ∂Measure.pi (fun _ : J => ν),
      (∫⁻x in ⋃j, A (labels j) (θ j), g x ∂μ) < ∞ := by
  have hcoordinate (j : J) : ∀ᵐθ ∂Measure.pi (fun _ : J => ν),
      (∫⁻x in A (labels j) (θ j), g x ∂μ) < ∞ :=
    (Measure.quasiMeasurePreserving_eval (fun _ : J => ν) j).ae (hfinite (labels j))
  filter_upwards [ae_all_iff.mpr hcoordinate] with θ hθ
  apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr fun j _ => hθ j

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_HyperspaceIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Closed continuum incidences in compact level graphs

The compatibility condition quantifies over subcontinua of a finite
level union. The hyperspace of nonempty compact sets is compact, and
connectedness, point membership and containment in a closed level graph
are closed conditions. Projection therefore preserves closedness for
continuum incidences with a fixed positive size witness.
-/

open Set TopologicalSpace Metric

namespace CircleDomainRigidity

theorem isClosed_connected_nonemptyCompacts {X : Type*} [MetricSpace X] :
    IsClosed {K : NonemptyCompacts X | IsConnected (K : Set X)} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro K hK
  have hn : ¬ IsPreconnected (K : Set X) := fun h => hK ⟨K.nonempty, h⟩
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed] at hn
  push Not at hn
  obtain ⟨A, B, hA, hB, hcover, hdisj, hnA, hnB⟩ := hn
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hdisj
  have hKU : ((K : Set X) ∩ U).Nonempty := by
    obtain ⟨x, hx, hxB⟩ := not_subset.mp hnB
    exact ⟨x, hx, hAU ((hcover hx).resolve_right hxB)⟩
  have hKV : ((K : Set X) ∩ V).Nonempty := by
    obtain ⟨x, hx, hxA⟩ := not_subset.mp hnA
    exact ⟨x, hx, hBV ((hcover hx).resolve_left hxA)⟩
  let N : Set (NonemptyCompacts X) :=
    {L | (L : Set X) ⊆ U ∪ V} ∩
      ({L | ((L : Set X) ∩ U).Nonempty} ∩ {L | ((L : Set X) ∩ V).Nonempty})
  refine ⟨N, ?_, ?_, ?_⟩
  · intro L hL hconn
    obtain ⟨x, _, hxU, hxV⟩ := hconn.isPreconnected U V hU hV hL.1 hL.2.1 hL.2.2
    exact Set.disjoint_left.mp hUV hxU hxV
  · exact (NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).inter
        (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV))
  · exact ⟨hcover.trans (union_subset_union hAU hBV), hKU, hKV⟩

theorem isClosed_nonemptyCompacts_membership {X : Type*} [MetricSpace X] :
    IsClosed {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} := by
  have heq : {p : X × NonemptyCompacts X | p.1 ∈ (p.2 : Set X)} =
      {p | infDist p.1 (p.2 : Set X) = 0} := by
    ext p
    exact p.2.isCompact.isClosed.mem_iff_infDist_zero p.2.nonempty
  rw [heq]
  exact isClosed_eq Metric.lipschitz_infDist.continuous continuous_const

theorem isClosed_compact_subset_graph
    {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) :
    IsClosed {p : NonemptyCompacts X × T | ∀ x ∈ (p.1 : Set X), (x, p.2) ∈ R} := by
  let F : NonemptyCompacts X × T → Compacts (X × T) :=
    fun p => p.1.toCompacts ×ˢ ({p.2} : Compacts T)
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have heq : {p : NonemptyCompacts X × T | ∀ x ∈ (p.1 : Set X), (x, p.2) ∈ R} =
      F ⁻¹' {K : Compacts (X × T) | (K : Set (X × T)) ⊆ R} := by
    ext p
    constructor
    · intro h
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have ht' : t = p.2 := ht
      subst t
      exact h x hx
    · intro h x hx
      exact h ⟨hx, rfl⟩
  rw [heq]
  exact (Compacts.isClosed_subsets_of_isClosed hR).preimage hF

/-- The compact hyperspace witnesses make each positive-size continuum
incidence a closed relation in the point and level parameters. -/
theorem isClosed_positiveContinuumIncidence
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) (ε : ℝ) :
    IsClosed (positiveContinuumIncidence R ε) := by
  let F : Set ((X × T) × (NonemptyCompacts X × (X × X))) :=
    {p | IsConnected (p.2.1 : Set X) ∧ p.1.1 ∈ (p.2.1 : Set X) ∧
      (∀ x ∈ (p.2.1 : Set X), (x, p.1.2) ∈ R) ∧
        p.2.2.1 ∈ (p.2.1 : Set X) ∧ p.2.2.2 ∈ (p.2.1 : Set X) ∧
          ε ≤ dist p.2.2.1 p.2.2.2}
  have hF : IsClosed F :=
    (isClosed_connected_nonemptyCompacts.preimage continuous_snd.fst).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_fst.fst.prodMk continuous_snd.fst)).inter
      ((isClosed_compact_subset_graph hR |>.preimage
        (continuous_snd.fst.prodMk continuous_fst.snd)).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_snd.snd.fst.prodMk continuous_snd.fst)).inter
      ((isClosed_nonemptyCompacts_membership.preimage
        (continuous_snd.snd.snd.prodMk continuous_snd.fst)).inter
      (isClosed_le continuous_const (continuous_snd.snd.fst.dist continuous_snd.snd.snd))))))
  have heq : positiveContinuumIncidence R ε = Prod.fst '' F := by
    ext p
    constructor
    · rintro ⟨K, hK, hx, hsub, u, hu, v, hv, hdist⟩
      exact ⟨(p, (K, (u, v))), ⟨hK, hx, hsub, hu, hv, hdist⟩, rfl⟩
    · rintro ⟨⟨p, K, u, v⟩, hp, rfl⟩
      exact ⟨K, hp.1, hp.2.1, hp.2.2.1, u, hp.2.2.2.1, v,
        hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace F hF

private theorem isClosed_connectedComponentIn_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (x : X) :
    IsClosed (connectedComponentIn A x) := by
  by_cases hx : x ∈ A
  · rw [connectedComponentIn_eq_image hx]
    exact hA.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

theorem nontrivialFiberComponentRelation_eq_iUnion
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    {R : Set (X × T)} (hR : IsClosed R) :
    nontrivialFiberComponentRelation R =
      ⋃ n : ℕ, positiveContinuumIncidence R (1 / ((n : ℝ) + 1)) := by
  ext p
  constructor
  · intro hp
    let A : Set X := {x | (x, p.2) ∈ R}
    change (connectedComponentIn A p.1).Nontrivial at hp
    have hx : p.1 ∈ A := by
      by_contra hx
      have he := connectedComponentIn_eq_empty hx
      exact Set.not_nontrivial_empty (he ▸ hp)
    have hA : IsClosed A := hR.preimage (continuous_id.prodMk continuous_const)
    let K : NonemptyCompacts X :=
      ⟨⟨connectedComponentIn A p.1,
        (isClosed_connectedComponentIn_of_isClosed hA p.1).isCompact⟩,
        ⟨p.1, mem_connectedComponentIn hx⟩⟩
    obtain ⟨u, hu, v, hv, huv⟩ := hp
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr huv)
    refine mem_iUnion.mpr ⟨n, K, isConnected_connectedComponentIn_iff.mpr hx,
      mem_connectedComponentIn hx, ?_, u, hu, v, hv, hn.le⟩
    exact fun _ hy => connectedComponentIn_subset A p.1 hy
  · intro hp
    obtain ⟨n, K, hK, hx, hsub, u, hu, v, hv, hdist⟩ := mem_iUnion.mp hp
    have hKsub := hK.isPreconnected.subset_connectedComponentIn hx hsub
    refine ⟨u, hKsub hu, v, hKsub hv, ?_⟩
    intro he
    have hpositive : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hzero : 0 < (0 : ℝ) := by simpa only [he, dist_self] using hpositive.trans_le hdist
    exact lt_irrefl 0 hzero

/-- The relation “the point belongs to a nondegenerate component of
the compact level fiber” is Fσ, hence Borel. -/
theorem measurableSet_nontrivialFiberComponentRelation
    {X T : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    [MeasurableSpace (X × T)] [BorelSpace (X × T)]
    {R : Set (X × T)} (hR : IsClosed R) :
    MeasurableSet (nontrivialFiberComponentRelation R) := by
  rw [nontrivialFiberComponentRelation_eq_iUnion hR]
  exact MeasurableSet.iUnion (fun n =>
    (isClosed_positiveContinuumIncidence hR (1 / ((n : ℝ) + 1))).measurableSet)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LevelIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite level unions and analytic compatibility failures

Repeated labels are allowed in a finite tuple of levels. Closed level
graphs give a closed union graph; its nondegenerate-component relation
is Borel by the compact hyperspace argument. After restriction to a
Borel set of free points, projection over the point is analytic.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem isClosed_finiteLevelUnionGraph
    {X T J Λ : Type*} [TopologicalSpace X] [TopologicalSpace T] [Fintype J]
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    IsClosed (finiteLevelUnionGraph R labels) := by
  apply isClosed_iUnion_of_finite
  intro j
  exact (hR (labels j)).preimage
    (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))

theorem measurableSet_finiteLevel_nontrivial_components
    {X T J Λ : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    [Fintype J] [MeasurableSpace X] [MeasurableSpace T]
    [BorelSpace X] [BorelSpace T] [SecondCountableTopology T]
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    MeasurableSet (nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)) :=
  measurableSet_nontrivialFiberComponentRelation (isClosed_finiteLevelUnionGraph hR labels)

/-- The failure event in (P) is an analytic subset of its finite level
parameter space. Its universal measurability is the separate classical
descriptive-set-theoretic input when completed measures are used. -/
theorem analyticSet_freeComponentFailure
    {X T J Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [TopologicalSpace T] [PolishSpace T] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace T] [BorelSpace X] [BorelSpace T]
    {F : Set X} (hF : MeasurableSet F) {Rnew : Set (X × T)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    AnalyticSet (freeComponentFailure F Rnew R labels) := by
  have hcomponents := measurableSet_finiteLevel_nontrivial_components hR labels
  have hbad : MeasurableSet {p : X × (T × (J → T)) |
      p.1 ∈ F ∧ (p.1, p.2.1) ∈ Rnew ∧
        (p.1, p.2.2) ∈ nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)} :=
    (hF.preimage measurable_fst).inter
      ((hnew.measurableSet.preimage (continuous_fst.prodMk continuous_snd.fst).measurable).inter
        (hcomponents.preimage (continuous_fst.prodMk continuous_snd.snd).measurable))
  exact hbad.analyticSet.image_of_continuous continuous_snd

/-- Fubini's null-section implication for a completed-measurable event.
This version does not require the event itself to be Borel. -/
theorem product_null_of_nullMeasurable_sections
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {E : Set (A × B)} (hE : NullMeasurableSet E (μ.prod ν))
    (hsections : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' E) = 0) :
    (μ.prod ν) E = 0 := by
  obtain ⟨t, htm, hst⟩ := hE
  rw [measure_congr hst, Measure.prod_apply htm]
  have hsec : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' t) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hst, hsections] with x hx h0
    calc ν (Prod.mk x ⁻¹' t) = ν (Prod.mk x ⁻¹' E) := (measure_congr hx).symm
      _ = 0 := h0
  rw [lintegral_congr_ae hsec]
  exact lintegral_zero

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

theorem contDiff_roundSphere_finite_chart :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) := by
  classical
  have hlin (W : Submodule ℝ RoundAmbient) (e : ℂ ≃L[ℝ] W) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (e z : RoundAmbient)) :=
    W.subtypeL.contDiff.comp e.contDiff
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux _ ∘ _)
  apply contDiff_stereoInvFunAux.comp
  exact hlin _ _

attribute [local instance] sphereMetric

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LinearChartWeight
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed linear coordinates in the sphere homeomorphism preserve
the inverse quadratic decay of stereographic derivatives. -/

noncomputable section

namespace CircleDomainRigidity

theorem linear_chart_inverse_quadratic_bound
    {v : RoundAmbient} (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  have hlin : ‖z‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A z‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      A.symm.toContinuousLinearMap.le_opNorm (A z)
  have hsq := pow_le_pow_left₀ (norm_nonneg z) hlin 2
  simp only [mul_pow] at hsq
  have hden : 1 + ‖z‖ ^ 2 ≤
      (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4) := by
    nlinarith [sq_nonneg ‖A.symm.toContinuousLinearMap‖, sq_nonneg ‖A z‖]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    _ ≤ (16 * ‖A.toContinuousLinearMap‖) *
        ((1 + ‖A.symm.toContinuousLinearMap‖ ^ 2) * (‖A z‖ ^ 2 + 4)) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = _ := by ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct image intersections with a closed set. Finite separated
image witnesses make this count Borel without counting repeated visits. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isClosed_separatedImageHits {H : Set X} (hH : IsClosed H) (n : ℕ) (r : ℝ) :
    IsClosed (separatedImageHits H n r) := by
  let E : Set (C(PathTime, X) × (Fin n → PathTime)) :=
    {p | (∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))) ∧
      ∀ i, p.1 (p.2 i) ∈ H}
  have he (i : Fin n) : Continuous (fun p : C(PathTime, X) × (Fin n → PathTime) =>
      p.1 (p.2 i)) := continuous_eval.comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hE : IsClosed E := by
    have hsep : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i j, i ≠ j → r ≤ dist (p.1 (p.2 i)) (p.1 (p.2 j))} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((he i).dist (he j))
    have hmem : IsClosed {p : C(PathTime, X) × (Fin n → PathTime) |
        ∀ i, p.1 (p.2 i) ∈ H} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => hH.preimage (he i)
    exact hsep.inter hmem
  have hp : Prod.fst '' E = separatedImageHits H n r := by
    ext γ
    constructor
    · rintro ⟨⟨_, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← hp]
  exact isClosedMap_fst_of_compactSpace E hE

theorem imageHitAtLeast_eq_iUnion (H : Set X) (n : ℕ) :
    imageHitAtLeast H n = ⋃ m : ℕ, separatedImageHits H n (1 / ((m : ℝ) + 1)) := by
  ext γ
  constructor
  · rintro ⟨t, ht, hH⟩
    obtain ⟨m, hm⟩ := exists_reciprocal_separation (γ ∘ t) ht
    exact mem_iUnion.mpr ⟨m, t, hm, hH⟩
  · intro h
    obtain ⟨m, t, ht, hH⟩ := mem_iUnion.mp h
    refine ⟨t, ?_, hH⟩
    intro i j he
    by_contra hij
    have hd := ht i j hij
    change γ (t i) = γ (t j) at he
    rw [he, dist_self] at hd
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

theorem pathImageCount_eq_iSup (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ = ⨆ n : ℕ,
      if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · rw [pathImageCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun x => x ∈ range γ ∩ H)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have hE (i : Fin (Fintype.card E)) : (e i).val ∈ range γ ∩ H :=
      (Finset.mem_filter.mp (e i).property).2
    choose t ht using fun i => (hE i).1
    have he : γ ∈ imageHitAtLeast H (Fintype.card E) := by
      refine ⟨t, ?_, fun i => (ht i).symm ▸ (hE i).2⟩
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact (ht i).symm.trans (hij.trans (ht j))
    have hn : (Fintype.card E : ℝ≥0∞) ≤ ⨆ n : ℕ,
        if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0 := by
      exact (ite_eq_left he).symm.le.trans (le_iSup
        (fun n : ℕ => if γ ∈ imageHitAtLeast H n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hn
  · apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, hH⟩ := hn
      have hm (i : Fin n) : γ (t i) ∈ range γ ∩ H := ⟨mem_range_self _, hH i⟩
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n,
            if γ (t i) ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0 := by
          simp only [hm, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ pathImageCount H γ := ENNReal.tsum_comp_le_tsum_of_injective ht
          (fun x => if x ∈ range γ ∩ H then (1 : ℝ≥0∞) else 0)
    · exact bot_le

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathImageCount {H : Set X} (hH : IsClosed H) :
    Measurable (pathImageCount H) := by
  change Measurable (fun γ => pathImageCount H γ)
  simp_rw [pathImageCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  rw [imageHitAtLeast_eq_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (isClosed_separatedImageHits hH n (1 / ((m : ℝ) + 1))).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathIntersectionMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite intersection measure of a random path with a closed set.
Closed incidence tests suffice for measurability of the whole measure.
Paths with infinitely many intersections are discarded; they form a null
set whenever the expected total intersection count is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathImageCount_eq_count (E : Set X) (hE : MeasurableSet E)
    (γ : C(PathTime, X)) :
    pathImageCount E γ = Measure.count (range γ ∩ E) := by
  have hs : MeasurableSet (range γ ∩ E) :=
    (isCompact_range γ.continuous).isClosed.measurableSet.inter hE
  rw [pathImageCount, Measure.count, Measure.sum_apply _ hs]
  congr 1
  funext x
  rw [Measure.dirac_apply' x hs]
  by_cases hx : x ∈ range γ ∩ E <;> simp [hx]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathIntersectionMeasure_finite (H : Set X) (hH : IsClosed H)
    (γ : C(PathTime, X)) : IsFiniteMeasure (pathIntersectionMeasure H γ) := by
  constructor
  by_cases h : pathImageCount H γ < ∞
  · simpa only [pathIntersectionMeasure, ite_eq_left h, Measure.restrict_apply_univ,
      ← pathImageCount_eq_count H hH.measurableSet γ] using h
  · simp [pathIntersectionMeasure, h]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathIntersectionMeasure_apply (H : Set X) (hH : IsClosed H)
    (E : Set X) (hE : MeasurableSet E)
    (γ : C(PathTime, X)) :
    pathIntersectionMeasure H γ E =
      if pathImageCount H γ < ∞ then pathImageCount (H ∩ E) γ else 0 := by
  by_cases h : pathImageCount H γ < ∞
  · rw [pathIntersectionMeasure, ite_eq_left h, ite_eq_left h, Measure.restrict_apply hE]
    rw [pathImageCount_eq_count (H ∩ E)]
    · congr 1
      ext x
      simp only [mem_inter_iff, and_comm, and_left_comm, and_assoc]
    · exact hH.measurableSet.inter hE
  · simp [pathIntersectionMeasure, h]

theorem measurable_pathIntersectionMeasure (H : Set X) (hH : IsClosed H) :
    Measurable (pathIntersectionMeasure H) := by
  let : ∀ γ : C(PathTime, X), IsFiniteMeasure (pathIntersectionMeasure H γ) :=
    pathIntersectionMeasure_finite H hH
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  · intro E hE
    simp_rw [pathIntersectionMeasure_apply H hH E hE.measurableSet]
    exact Measurable.ite ((measurable_pathImageCount hH) measurableSet_Iio)
      (measurable_pathImageCount (hH.inter hE)) measurable_const
  · simp_rw [pathIntersectionMeasure_apply H hH univ MeasurableSet.univ,
      inter_univ]
    exact Measurable.ite ((measurable_pathImageCount hH) measurableSet_Iio)
      (measurable_pathImageCount hH) measurable_const

theorem meanPathIntersectionMeasure_apply (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞)
    (E : Set X) (hE : MeasurableSet E) :
    meanPathIntersectionMeasure H μ E = ∫⁻ γ, pathImageCount (H ∩ E) γ ∂μ := by
  rw [meanPathIntersectionMeasure,
    Measure.bind_apply hE (measurable_pathIntersectionMeasure H hH).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_lt_top (measurable_pathImageCount hH) hfinite.ne] with γ hγ
  rw [pathIntersectionMeasure_apply H hH E hE, ite_eq_left hγ]

theorem meanPathIntersectionMeasure_finite (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞) :
    IsFiniteMeasure (meanPathIntersectionMeasure H μ) := by
  constructor
  simpa only [meanPathIntersectionMeasure_apply H hH μ hfinite univ MeasurableSet.univ,
    inter_univ] using hfinite

theorem meanPathIntersectionMeasure_apply_subset (H : Set X) (hH : IsClosed H)
    (μ : Measure C(PathTime, X))
    (hfinite : (∫⁻ γ, pathImageCount H γ ∂μ) < ∞)
    (E : Set X) (hE : MeasurableSet E) (hEH : E ⊆ H) :
    meanPathIntersectionMeasure H μ E = ∫⁻ γ, pathImageCount E γ ∂μ := by
  rw [meanPathIntersectionMeasure_apply H hH μ hfinite E hE,
    inter_eq_right.mpr hEH]

theorem meanPathIntersectionMeasure_map_null
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (a : Y → C(PathTime, X)) (ha : Measurable a)
    (H : Set X) (hH : IsClosed H) (E : Set X) (hE : MeasurableSet E)
    (hmiss : ∀ᵐ y ∂μ, Disjoint (range (a y) ∩ H) E) :
    meanPathIntersectionMeasure H (μ.map a) E = 0 := by
  have hm : Measurable (fun γ => pathIntersectionMeasure H γ E) :=
    (Measure.measurable_coe hE).comp (measurable_pathIntersectionMeasure H hH)
  rw [meanPathIntersectionMeasure, Measure.bind_apply hE
    (measurable_pathIntersectionMeasure H hH).aemeasurable,
    lintegral_map hm ha]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hmiss] with y hy
  by_cases h : pathImageCount H (a y) < ∞
  · rw [pathIntersectionMeasure, ite_eq_left h, Measure.restrict_apply hE]
    have he : E ∩ (range (a y) ∩ H) = ∅ := hy.symm.eq_bot
    rw [he, measure_empty]
    rfl
  · simp [pathIntersectionMeasure, h]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleIncrementContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous families of circle paths have continuous real increments.
This follows from the actual homotopy lift, so no choice of a discontinuous
starting-angle representative enters the continuity or compact bounds. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem compact_circle_increment_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, |circlePathIncrement γ| ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image continuous_circlePathIncrement).isBounded.exists_norm_le
  exact ⟨M, fun γ hγ => by simpa only [Real.norm_eq_abs] using hM _ (mem_image_of_mem _ hγ)⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CirclePathPrefixes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for all initial lifts in a compact family of circle paths. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem continuous_circlePathPrefix :
    Continuous (fun p : C(unitInterval, UnitAddCircle) × unitInterval =>
      circlePathPrefix p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_snd.mul (continuous_snd.comp continuous_fst)))

theorem circlePathIncrement_prefix (γ : C(unitInterval, UnitAddCircle)) (t : unitInterval) :
    circlePathIncrement (circlePathPrefix γ t) =
      realCirclePathLift γ t - realCirclePathLift γ 0 := by
  let u := (realCirclePathLift γ).comp
    (⟨fun s : unitInterval => s * t, continuous_id.mul continuous_const⟩ :
      C(unitInterval, unitInterval))
  rw [circlePathIncrement_eq_lift (circlePathPrefix γ t) u
    (fun s => realCirclePathLift_projects γ (s * t))]
  simp only [u, ContinuousMap.comp_apply, ContinuousMap.coe_mk, one_mul, zero_mul]

theorem compact_circle_path_lifts_bounded
    (K : Set C(unitInterval, UnitAddCircle)) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ γ ∈ K, ∀ t : unitInterval, |realCirclePathLift γ t| ≤ M := by
  obtain ⟨M, hM⟩ := compact_circle_increment_bounded _
    ((hK.prod isCompact_univ).image continuous_circlePathPrefix)
  refine ⟨M + 1, fun γ hγ t => ?_⟩
  have hb : |realCirclePathLift γ t - realCirclePathLift γ 0| ≤ M := by
    rw [← circlePathIncrement_prefix]
    exact hM _ ⟨(γ, t), ⟨hγ, mem_univ _⟩, rfl⟩
  have hstart : realCirclePathLift γ 0 = circleRepresentative (γ 0) := by
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero _ _ _
  have hr := (AddCircle.equivIco (1 : ℝ) 0 (γ 0)).property
  have hs : |realCirclePathLift γ 0| ≤ 1 := by
    rw [hstart]
    change |((AddCircle.equivIco (1 : ℝ) 0 (γ 0)).val)| ≤ 1
    rw [abs_of_nonneg hr.1]
    simpa only [zero_add] using hr.2.le
  calc
    |realCirclePathLift γ t| =
        |(realCirclePathLift γ t - realCirclePathLift γ 0) + realCirclePathLift γ 0| := by
          congr 1; ring
    _ ≤ |realCirclePathLift γ t - realCirclePathLift γ 0| + |realCirclePathLift γ 0| := abs_add_le _ _
    _ ≤ M + 1 := add_le_add hb hs

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableArcIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel version of the explicit index, including a value on the
coincidence set. Its deck identity holds everywhere, before averaging. -/

open Set Function Filter MeasureTheory
open scoped Topology Classical

/-! d13f23b's Borel structure on `C(X, Y)` (missing in our Mathlib), with `measurable_iff_eval`
proved here for a compact metric domain. -/

theorem _root_.ContinuousMap.measurable_iff_eval {X Y Z : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace Z] {g : Z → C(X, Y)} :
    Measurable g ↔ ∀ x, Measurable fun z => g z x := by
  refine ⟨fun h x => (continuous_eval_const x).measurable.comp h, fun h => ?_⟩
  obtain ⟨D, hDc, hDd⟩ := _root_.TopologicalSpace.exists_countable_dense X
  have hcl : ∀ (f : C(X, Y)) (s : ℝ), MeasurableSet {z | dist (g z) f ≤ s} := by
    intro f s
    rcases lt_or_ge s 0 with hs | hs
    · have : {z | dist (g z) f ≤ s} = ∅ :=
        Set.eq_empty_of_forall_notMem fun z hz => absurd (lt_of_le_of_lt dist_nonneg (lt_of_le_of_lt hz hs)) (lt_irrefl _)
      rw [this]; exact MeasurableSet.empty
    have heq : {z | dist (g z) f ≤ s} = ⋂ x ∈ D, {z | dist (g z x) (f x) ≤ s} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [ContinuousMap.dist_le hs]
      refine ⟨fun H x _ => H x, fun H x => ?_⟩
      have hc : IsClosed {x | dist (g z x) (f x) ≤ s} :=
        isClosed_le ((g z).continuous.dist f.continuous) continuous_const
      have : closure D ⊆ {x | dist (g z x) (f x) ≤ s} :=
        hc.closure_subset_iff.mpr (fun x hx => H x hx)
      exact this (hDd.closure_eq ▸ Set.mem_univ x)
    rw [heq]
    exact MeasurableSet.biInter hDc fun x _ =>
      measurableSet_le ((h x).dist measurable_const) measurable_const
  have hball : ∀ (f : C(X, Y)) (r : ℝ), MeasurableSet (g ⁻¹' Metric.ball f r) := by
    intro f r
    have : g ⁻¹' Metric.ball f r = ⋃ n : ℕ, {z | dist (g z) f ≤ r - 1 / (n + 1)} := by
      ext z
      simp only [Set.mem_preimage, Metric.mem_ball, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / (n + 1) := by positivity
        linarith
    rw [this]
    exact MeasurableSet.iUnion fun n => hcl f _
  refine measurable_of_isOpen fun U hU => ?_
  have hε : ∀ f : U, ∃ ε > 0, Metric.ball (f : C(X, Y)) ε ⊆ U := fun f =>
    Metric.isOpen_iff.mp hU f f.2
  choose ε hεpos hεU using hε
  obtain ⟨T, hTc, hT⟩ := _root_.TopologicalSpace.isOpen_iUnion_countable
    (fun f : U => Metric.ball (f : C(X, Y)) (ε f)) (fun _ => Metric.isOpen_ball)
  have hU' : U = ⋃ f ∈ T, Metric.ball (f : C(X, Y)) (ε f) := by
    rw [hT]
    ext h
    simp only [Set.mem_iUnion]
    refine ⟨fun hh => ⟨⟨h, hh⟩, Metric.mem_ball_self (hεpos _)⟩, fun ⟨f, hf⟩ => hεU f hf⟩
  rw [hU', Set.preimage_iUnion₂]
  exact MeasurableSet.biUnion hTc fun f _ => hball _ _


noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_circleRepresentative_dup1 : Measurable circleRepresentative := by
  exact measurable_unitCircleCut

end CircleDomainRigidity.FiniteTransfer

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
-- module Solutions.Q146_CD.CircleDomains_Probability_ArcNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From simple-arc payment to null trace images

Distinct points of a connected open subset of a locally connected metric
continuum can be joined there by a simple arc. The arc-existence hypothesis
is the local arcwise-connectedness theorem used by Lorimer (1981),
*Locally compact Hjelmslev planes and rings*, proof of Lemma 3.2,
pp. 1002–1003, displayed (*), DOI 10.4153/CJM-1981-077-5.
The null-image criterion derives the measure-theoretic conclusion from
this topological hypothesis and the simple-arc payment inequality.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

/-- The null-image criterion with the actual simple-arc payment premise.
The input only supplies arcs; no oscillation or null-image conclusion
is included in it. -/
theorem null_image_of_simple_arc_payment
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [μ.OuterRegular] (harcs : HasSimpleArcsInConnectedOpens X)
    {F V : Set X} (hV : IsOpen V) (hF : μ (F ∩ V) = 0)
    (v : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hpay : ∀ x ∈ F ∩ V, ∀ y ∈ F ∩ V,
      ∀ γ : Path x y, Function.Injective γ → range γ ⊆ V →
        |v x - v y| ≤ A * μ.real (range γ)) :
    volume (v '' (F ∩ V)) = 0 := by
  apply null_image_inter_open_of_connected_open_oscillation hV hF v hA
  intro U hUV hU hconn x hx y hy
  by_cases hxy : x = y
  · subst y
    simpa only [sub_self, abs_zero] using
      mul_nonneg hA (measureReal_nonneg (μ := μ) (s := U))
  obtain ⟨γ, hγ, hγU⟩ := harcs U hU hconn x hx.2 y hy.2 hxy
  exact (hpay x ⟨hx.1, hUV hx.2⟩ y ⟨hy.1, hUV hy.2⟩ γ hγ
    (hγU.trans hUV)).trans
      (mul_le_mul_of_nonneg_left (measureReal_mono hγU) hA)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCentering
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit disk automorphism used to move the marked endpoint to
the origin in a Jordan disk coordinate. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section
namespace CircleDomainRigidity

theorem diskCentering_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  have hnorm : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt (by simpa using ha)
  intro h
  rw [(sub_eq_zero.mp h).symm, norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem diskCentering_normSq_identity (a z : ℂ) :
    Complex.normSq (1 - conj a * z) - Complex.normSq (z - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem diskCentering_norm_le {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskCentering a z‖ ≤ 1 := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 ≤ ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_nonneg ha2 hz2]
  have hn : ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz))).mpr hn

theorem diskCentering_norm_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskCentering a z‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hi := diskCentering_normSq_identity a z
  simp only [← Complex.sq_norm] at hi
  have hsq : ‖z - a‖ ^ 2 < ‖1 - conj a * z‖ ^ 2 := by
    nlinarith [mul_pos ha2 hz2]
  have hn : ‖z - a‖ < ‖1 - conj a * z‖ := by
    nlinarith [norm_nonneg (z - a), norm_nonneg (1 - conj a * z)]
  rw [diskCentering, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr (diskCentering_den_ne_zero ha hz.le))).mpr hn

theorem diskCentering_inverse {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskCentering (-a) (diskCentering a z) = z := by
  have hden := diskCentering_den_ne_zero ha hz
  have haa := diskCentering_den_ne_zero ha ha.le
  have hneg : ‖-a‖ < 1 := by simpa only [norm_neg] using ha
  have hout := diskCentering_den_ne_zero hneg (diskCentering_norm_le ha hz)
  unfold diskCentering at hout ⊢
  simp only [map_neg, neg_mul, sub_neg_eq_add] at hout ⊢
  have haux : 1 + conj a * ((z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    field_simp
    ring
  rw [haux]
  have hden' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  have haa' : 1 - a * conj a ≠ 0 := by simpa only [mul_comm] using haa
  field_simp [hden, hden', haa, haa']
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCenteringHomeomorph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centering formula is an actual homeomorphism of the closed disk. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem diskCentering_injOn (a : ℂ) (ha : ‖a‖ < 1) :
    InjOn (diskCentering a) (closedBall (0 : ℂ) 1) := by
  intro z hz w hw h
  have he := congrArg (diskCentering (-a)) h
  rwa [diskCentering_inverse ha (mem_closedBall_zero_iff.mp hz),
    diskCentering_inverse ha (mem_closedBall_zero_iff.mp hw)] at he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereJordanCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem sphereJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) :
    InjOn (sphereJordanCoordinate K) (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy h
  rw [closure_sphere_image_jordanInterior] at hx hy
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact congrArg ((↑) : ℂ → Sphere) (K.symm.injective h)

theorem sphereJordanCoordinate_mapsTo (K : ℂ ≃ₜ ℂ) :
    MapsTo (sphereJordanCoordinate K)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) (closedBall 0 1) := by
  intro x hx
  rw [closure_sphere_image_jordanInterior, closure_jordanInterior] at hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply] using hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CenteredJordanCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered disk coordinates for the actual spherical Jordan collars.
The continuous extension is used only to push path laws to path space. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem sphereJordanCoordinate_norm_lt (K : ℂ ≃ₜ ℂ) {x : Sphere}
    (hx : x ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ‖sphereJordanCoordinate K x‖ < 1 := by
  obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply,
    mem_ball_zero_iff] using hw

theorem centeredJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    InjOn (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy he
  apply sphereJordanCoordinate_injOn K hx hy
  exact diskCentering_injOn _ (sphereJordanCoordinate_norm_lt K hb)
    (sphereJordanCoordinate_mapsTo K hx) (sphereJordanCoordinate_mapsTo K hy) he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredArcLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the constructed terminal arc law to centered disk coordinates.
The coordinate extension is only evaluated on the closed collar. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

lemma terminalArcSet_mapsTo_closure {V : Set Sphere} {b : Sphere}
    {γ : C(PathTime, Sphere)} (hγ : γ ∈ terminalArcSet V b) (hb : b ∈ V) :
    MapsTo γ univ (closure V) := by
  intro t _
  by_cases h0 : t = ⊥
  · exact h0 ▸ frontier_subset_closure hγ.2.1
  by_cases h1 : t = ⊤
  · exact h1 ▸ hγ.2.2.1.symm ▸ subset_closure hb
  exact subset_closure (hγ.2.2.2 ⟨lt_of_le_of_ne bot_le (Ne.symm h0),
    lt_of_le_of_ne le_top h1⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DiskStartLaw
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Atomlessness and the boundary measure for the actual disk arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem normalizedArgument_injOn_unit_sphere :
    InjOn normalizedArgument {z : ℂ | ‖z‖ = 1} := by
  intro z hz w hw h
  apply Complex.ext_norm_arg (hz.trans hw.symm)
  apply Complex.arg_coe_angle_eq_iff.mp
  exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_CayleyBoundaryOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real boundary of the half-plane is sent monotonically to the
positively oriented circle cut at the point at infinity. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem cayleyBoundary_ne_one (x : ℝ) : halfPlaneDisk x ≠ 1 :=
  halfPlaneDisk_ne_one (by simp)

theorem continuous_cayleyBoundaryAngle : Continuous cayleyBoundaryAngle := by
  have hM : Continuous (fun x : ℝ => halfPlaneDisk x) :=
    continuousOn_halfPlaneDisk.comp_continuous Complex.continuous_ofReal (by intro x; simp)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hn : halfPlaneDisk (x : ℂ) ≠ 0 := by
    intro he
    have hh := cayleyBoundary_norm x
    rw [he, norm_zero] at hh
    exact zero_ne_one hh
  have hzero : normalizedArgument (halfPlaneDisk x) ≠ (0 : ℝ) := by
    intro he
    apply cayleyBoundary_ne_one x
    rw [← standardCirclePoint_normalizedArgument (cayleyBoundary_norm x), he,
      AddCircle.coe_zero, standardCirclePoint_zero]
  exact continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) 0 hzero).comp
      (f := fun y : ℝ => normalizedArgument (halfPlaneDisk y))
      ((continuousAt_normalizedArgument hn).comp (f := fun y : ℝ => halfPlaneDisk y) hM.continuousAt))

theorem cayleyBoundaryAngle_injective : Injective cayleyBoundaryAngle := by
  intro x y he
  have ha := normalizedArgument_injOn_unit_sphere (cayleyBoundary_norm x)
    (cayleyBoundary_norm y) (unitCircleCut_injective he)
  exact Complex.ofReal_injective (halfPlaneDisk_injOn (by simp) (by simp) ha)

theorem cayleyBoundaryAngle_zero : cayleyBoundaryAngle 0 = 1 / 2 := by
  have hM : halfPlaneDisk 0 = -1 := by simp [halfPlaneDisk]
  have hπ : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_zero, hM, normalizedArgument_eq, Complex.arg_neg_one, hπ]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem cayleyBoundaryAngle_one : cayleyBoundaryAngle 1 = 3 / 4 := by
  have hM : halfPlaneDisk 1 = -Complex.I := by
    unfold halfPlaneDisk
    apply (div_eq_iff (halfPlaneDisk_den_ne_zero (z := 1) (by simp))).mpr
    rw [mul_add]
    simp only [neg_mul, mul_one, Complex.I_mul_I, neg_neg]
    ring
  have hπ : -(Real.pi / 2) / (2 * Real.pi) = -(1 / 4) := by field_simp <;> ring
  have hc : ((-(1 / 4) : ℝ) : UnitAddCircle) = ((3 / 4 : ℝ) : UnitAddCircle) :=
    (addCircle_eq_iff_exists_int 1 _ _).mpr ⟨-1, by norm_num⟩
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_one, hM, normalizedArgument_eq, Complex.arg_neg_I, hπ, hc]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (3 / 4 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem strictMono_cayleyBoundaryAngle : StrictMono cayleyBoundaryAngle := by
  rcases continuous_cayleyBoundaryAngle.strictMono_of_inj cayleyBoundaryAngle_injective with h | h
  · exact h
  · have hh := h (show (0 : ℝ) < 1 by norm_num)
    rw [cayleyBoundaryAngle_zero, cayleyBoundaryAngle_one] at hh
    norm_num at hh

theorem cayleyBoundary_mem_closingArc (a x : ℝ) :
    halfPlaneDisk x ∈ range (boundaryClosingArc (halfPlaneDisk a) (cayleyBoundary_norm a)) ↔ x ≤ a := by
  let A := cayleyBoundaryAngle a
  have hA : 0 < A := boundary_angle_pos (cayleyBoundary_norm a) (cayleyBoundary_ne_one a)
  constructor
  · rintro ⟨t, ht⟩
    have hc := congrArg normalizedArgument ht
    change normalizedArgument (standardCirclePoint ((A * (t : ℝ) : ℝ) : UnitAddCircle)) =
      normalizedArgument (halfPlaneDisk x) at hc
    rw [normalizedArgument_standardCirclePoint] at hc
    have hb := boundary_arc_parameter_mem (cayleyBoundary_norm a) (cayleyBoundary_ne_one a) t
    change A * (t : ℝ) ∈ Ico (0 : ℝ) 1 at hb
    have hqx : cayleyBoundaryAngle x = A * (t : ℝ) := by
      unfold cayleyBoundaryAngle unitCircleCut
      rw [← hc]
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show A * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by simpa only [zero_add] using hb))
    apply strictMono_cayleyBoundaryAngle.le_iff_le.mp
    rw [hqx]
    exact mul_le_of_le_one_right hA.le t.property.2
  · intro hxa
    have hqx : cayleyBoundaryAngle x ≤ A := strictMono_cayleyBoundaryAngle.monotone hxa
    let t : PathTime := ⟨cayleyBoundaryAngle x / A,
      div_nonneg (unitCircleCut_mem _).1 hA.le, (div_le_one hA).mpr hqx⟩
    refine ⟨t, ?_⟩
    change standardCirclePoint ((A * (cayleyBoundaryAngle x / A) : ℝ) : UnitAddCircle) = _
    rw [mul_div_cancel₀ _ hA.ne']
    change standardCirclePoint ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) = _
    rw [show ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) =
      normalizedArgument (halfPlaneDisk x) from AddCircle.coe_equivIco]
    exact standardCirclePoint_normalizedArgument (cayleyBoundary_norm x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactArcWinding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform winding bounds for initial portions of a compact simple-arc
family, in any continuous angular coordinate on the punctured plane. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

theorem compact_initial_arc_lifts_bounded
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (b : ℂ)
    (hinj : ∀ γ ∈ K, Injective γ) (hend : ∀ γ ∈ K, γ ⊤ = b)
    (q : C({x : ℂ // x ≠ b}, UnitAddCircle)) (c : PathTime) (hc : c < ⊤) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : unitInterval,
      |realCirclePathLift (initialArcAngles q γ.val (hinj _ γ.property)
        (hend _ γ.property) c hc) t| ≤ M := by
  let F : K → C(unitInterval, UnitAddCircle) := fun γ =>
    initialArcAngles q γ.val (hinj _ γ.property) (hend _ γ.property) c hc
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply q.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_snd.mul continuous_const))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := compact_circle_path_lifts_bounded (range F) (isCompact_range hF)
  exact ⟨M, fun γ t => hM (F γ) (mem_range_self γ) t⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactDiskRayBounds
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-depth part of a compact family of disk rays lies in a
common initial time interval, on which the angular lifts are uniformly bounded. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_initial_angle_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) {r : ℝ} (hr : 0 < r) :
    ∃ (c : PathTime) (hc : c < ⊤) (M : ℝ),
      0 < c ∧
      (∀ γ ∈ K, ∀ t, r ≤ ‖γ t‖ → t < c) ∧
      ∀ γ : K, ∀ t : unitInterval,
        |realCirclePathLift (initialArcAngles puncturedArgument γ.val
          (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) t| ≤ M := by
  obtain ⟨c, hc0, hc1, htail⟩ := compact_disk_rays_uniform_tail K hK
    (fun γ hγ => (hKS hγ).2.2.1) hr
  have hc : c < ⊤ := hc1
  obtain ⟨M, hM⟩ := compact_initial_arc_lifts_bounded K hK 0
    (fun γ hγ => (hKS hγ).1) (fun γ hγ => (hKS hγ).2.2.1)
    puncturedArgument c hc
  refine ⟨c, hc, M, hc0, ?_, hM⟩
  intro γ hγ t ht
  by_contra! hct
  exact (not_lt_of_ge ht) (htail γ hγ t hct)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayLift
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous lift of each actual terminal arc to angular and logarithmic
coordinates. The angular origin is the representative of the arc start. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayAngle_mul_prefix (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = 0)
    (c : DiskRayTime) (u : unitInterval) :
    diskRayAngle γ hi he ⟨u * c.val, (unitInterval.mul_le_right.trans_lt c.property)⟩ =
      realCirclePathLift (initialArcAngles puncturedArgument γ hi he c.val c.property) u := by
  let A := initialArcAngles puncturedArgument γ hi he c.val c.property
  have hp : initialArcAngles puncturedArgument γ hi he (u * c.val)
      (unitInterval.mul_le_right.trans_lt c.property) = circlePathPrefix A u := by
    ext s
    change normalizedArgument (γ (s * (u * c.val))) = normalizedArgument (γ ((s * u) * c.val))
    rw [mul_assoc]
  rw [diskRayAngle_eq_increment, hp, circlePathIncrement_prefix]
  have h0 : realCirclePathLift A 0 = circleRepresentative (normalizedArgument (γ 0)) := by
    rw [realCirclePathLift, (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero]
    simp only [A, initialArcAngles, puncturedArgument, ContinuousMap.coe_mk, zero_mul]
  rw [h0]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayProper
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform properness and angular bounds on every bounded-depth strip
for the lifted compact disk-arc family. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem compact_disk_rays_angle_bound_on_strip
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (Y : ℝ) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : DiskRayTime, diskRayDepth γ.val t ≤ Y →
      |diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t| ≤ M := by
  obtain ⟨c, hc, M, hc0, htime, hM⟩ :=
    compact_disk_rays_initial_angle_bound K hK hKS (Real.exp_pos (-Y))
  refine ⟨M, fun γ t ht => ?_⟩
  have hp : 0 < ‖γ.val t.val‖ := norm_pos_iff.mpr
    (diskRay_nonzero γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t)
  have hnorm : Real.exp (-Y) ≤ ‖γ.val t.val‖ := by
    apply (Real.le_log_iff_exp_le hp).mp
    change -Real.log ‖γ.val t.val‖ ≤ Y at ht
    linarith
  have htc := htime γ.val γ.property t.val hnorm
  have hcp : (0 : ℝ) < c := hc0
  let u : unitInterval := ⟨(t.val : ℝ) / (c : ℝ),
    div_nonneg t.val.property.1 hcp.le, (div_le_one hcp).mpr htc.le⟩
  have hut : u * c = t.val := by
    apply Subtype.ext
    exact div_mul_cancel₀ _ hcp.ne'
  have he : (⟨u * c, unitInterval.mul_le_right.trans_lt hc⟩ : DiskRayTime) = t :=
    Subtype.ext hut
  have ha := diskRayAngle_mul_prefix γ.val (hKS γ.property).1
    (hKS γ.property).2.2.1 (⟨c, hc⟩ : DiskRayTime) u
  have hat : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 t =
      realCirclePathLift (initialArcAngles puncturedArgument γ.val
        (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) u := by
    simpa only [he] using ha
  exact (congrArg abs hat).symm ▸ hM γ u

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayTranslates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Different integer translates of a lifted simple disk arc are disjoint. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem diskRayTime_eq_of_coordinates (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (s t : DiskRayTime)
    (hangle : (diskRayAngle γ hi he s : UnitAddCircle) = diskRayAngle γ hi he t)
    (hdepth : diskRayDepth γ s = diskRayDepth γ t) : s = t := by
  apply Subtype.ext
  apply hi
  apply Complex.ext_norm_arg
  · have hd : Real.log ‖γ s.val‖ = Real.log ‖γ t.val‖ := neg_injective hdepth
    have hexp := congrArg Real.exp hd
    simpa only [Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he s)),
      Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hi he t))] using hexp
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    exact (diskRayAngle_projects γ hi he s).symm.trans
      (hangle.trans (diskRayAngle_projects γ hi he t))

theorem translatedDiskRay_eq_iff (γ : C(PathTime, ℂ))
    (hi : Injective γ) (he : γ ⊤ = 0) (k l : ℤ) (s t : DiskRayTime) :
    translatedDiskRay γ hi he k s = translatedDiskRay γ hi he l t ↔ k = l ∧ s = t := by
  constructor
  · intro h
    have ha : diskRayAngle γ hi he s + (k : ℝ) = diskRayAngle γ hi he t + (l : ℝ) :=
      congrArg Prod.fst h
    have hd : diskRayDepth γ s = diskRayDepth γ t := congrArg Prod.snd h
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    have hl : ((l : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (l : ℝ) 0).mpr ⟨l, by simp⟩
    have hs : s = t := diskRayTime_eq_of_coordinates γ hi he s t (by
      have hc := congrArg (fun x : ℝ => (x : UnitAddCircle)) ha
      simpa only [AddCircle.coe_add, hk, hl, add_zero] using hc) hd
    subst t
    exact ⟨Int.cast_injective (add_left_cancel ha), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayJordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compactified lifted ray bounds a Jordan disk after closing
along the positive boundary arc. Its entire filling stays in the unit disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem jordan_fill_subset_closed_unitDisk (H : ℂ ≃ₜ ℂ)
    (hf : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 1) :
    closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  apply closed_jordanInterior_subset_of_unbounded_connected_compl H
  · simpa only [jordanInterior, Homeomorph.refl_apply, image_id,
      closure_ball _ one_ne_zero]
      using (isConnected_exterior_jordanInterior (Homeomorph.refl ℂ)).isPreconnected
  · intro hb
    apply NormedSpace.unbounded_univ ℝ ℂ
    have h := (isCompact_closedBall (0 : ℂ) 1).isBounded.union hb
    simpa only [union_compl_self] using h
  · intro z hz
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hf z hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskBoundarySide
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the crosscut, a boundary arc of a filling has a whole relative
neighborhood in the closed disk on the same side. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem closed_disk_neighborhood_in_filling
    (H : ℂ ≃ₜ ℂ) (hU : jordanInterior H ⊆ Metric.ball 0 1)
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {ε : ℝ} (hε : 0 < ε)
    (hfront : Metric.ball x ε ∩ frontier (jordanInterior H) ⊆ Metric.sphere 0 1) :
    Metric.ball x ε ∩ Metric.closedBall 0 1 ⊆ closure (jordanInterior H) := by
  have hC : IsPreconnected (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1) :=
    ((convex_ball x ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  have hmiss : Disjoint (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1)
      (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    intro z hz hf
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ⟨hz.1, hf⟩)
    have hl : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz.2
    exact (ne_of_lt hl) hn
  have hsplit : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H ∨
      Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ (closure (jordanInterior H))ᶜ := by
    apply hC.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact disjoint_compl_right.mono_left subset_closure
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        apply Set.disjoint_left.mp hmiss hz
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hc, hi⟩
  have hinside : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H := by
    rcases hsplit with hi | ho
    · exact hi
    · obtain ⟨z, hzB, hzU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hx)
        (Metric.ball x ε) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
      exact (ho ⟨hzB, hU hzU⟩ (subset_closure hzU)).elim
  intro z hz
  apply closure_mono hinside
  apply Metric.isOpen_ball.inter_closure
  simpa only [closure_ball _ one_ne_zero] using hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneRay
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactification of the integer translates of a lifted ray. The curve
escapes in height, so the added endpoint is the single boundary point 1. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem translatedHalfPlaneRay_meet_iff (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k l : ℤ) (s t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t ↔
      k = l ∧ s = t := by
  have he : ((translatedHalfPlaneRay γ hγ k).curve s = (translatedHalfPlaneRay γ hγ l).curve t) ↔
      translatedDiskRay γ hγ.1 hγ.2.2.1 k s = translatedDiskRay γ hγ.1 hγ.2.2.1 l t := by
    constructor
    · intro h
      apply Prod.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.re h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Complex.im h
    · intro h
      apply Complex.ext
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.fst h
      · simpa [translatedHalfPlaneRay, diskRayComplex, translatedDiskRay, diskRayLift] using congrArg Prod.snd h
  exact he.trans (translatedDiskRay_eq_iff γ hγ.1 hγ.2.2.1 k l s t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RayJordanSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side functions for all integer translates of a lifted ray. Boundary
order is the ordinary order on the real boundary of the half-plane. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem crosscut_norm_le (R : HalfPlaneRay) (t : PathTime) : ‖R.crosscut t‖ ≤ 1 := by
  by_cases ht : t < ⊤
  · change ‖R.compactify t‖ ≤ 1
    rw [compactify, dite_eq_left ht]
    exact halfPlaneDisk_norm_le (R.nonneg _)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    change ‖R.compactify ⊤‖ ≤ 1
    rw [R.compactify_top, norm_one]

theorem filling_subset (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    closure (jordanInterior H) ⊆ Metric.closedBall 0 1 ∧
      jordanInterior H ⊆ Metric.ball 0 1 := by
  have hcl : closure (jordanInterior H) ⊆ Metric.closedBall 0 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hH] at hz
    rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact R.crosscut_norm_le t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨hcl, ?_⟩
  have hi := interior_mono hcl
  rwa [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hi

theorem isLocallyConstant_side (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    IsLocallyConstant (R.side H) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  by_cases hz : z.val ∈ closure (jordanInterior H)
  · have hn : ∃ ε > 0, Metric.ball z.val ε ∩ Metric.closedBall 0 1 ⊆
        closure (jordanInterior H) := by
      by_cases hi : z.val ∈ jordanInterior H
      · obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z.val hi
        exact ⟨ε, hε, fun _ h => subset_closure (hB h.1)⟩
      · have hf : z.val ∈ frontier (jordanInterior H) := by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hz, hi⟩
        obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp
          (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl z.val z.property.2
        refine ⟨ε, hε, closed_disk_neighborhood_in_filling H (R.filling_subset hH).2 hf hε ?_⟩
        rintro w ⟨hw, hwf⟩
        rw [hH] at hwf
        rcases hwf with hwc | ⟨t, rfl⟩
        · exact (hB hw hwc).elim
        · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm _ _ t)
    obtain ⟨ε, hε, hB⟩ := hn
    have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ Metric.ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_left hz, ite_eq_left (hB ⟨hw, w.property.1⟩)]
  · have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ (closure (jordanInterior H))ᶜ :=
      continuous_subtype_val.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hz)
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_right hz, ite_eq_right hw]

theorem start_eq_real (R : HalfPlaneRay) :
    R.compactify 0 = halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
  have ht : (0 : PathTime) < ⊤ := bot_lt_top
  rw [compactify, dite_eq_left ht]
  congr 1
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using R.start

theorem side_boundary (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    (x : ℝ) (hmiss : halfPlaneDisk x ∉ range R.crosscut) :
    R.side H ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), hmiss⟩ =
      if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hnot : halfPlaneDisk x ∉ jordanInterior H := by
    intro hi
    have hl : ‖halfPlaneDisk x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (R.filling_subset hH).2 hi
    rw [cayleyBoundary_norm] at hl
    exact lt_irrefl _ hl
  have hc : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ x ≤ (R.curve ⟨0, bot_lt_top⟩).re := by
    have he : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ halfPlaneDisk x ∈ frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      simp only [Set.mem_sdiff, hnot, not_false_eq_true, and_true]
    rw [he, hH, mem_union, or_iff_right hmiss]
    have hb := cayleyBoundary_mem_closingArc (R.curve ⟨0, bot_lt_top⟩).re x
    have heq : (fun t : PathTime => boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) =
        (fun t : PathTime => boundaryClosingArc
          (halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ))
          (cayleyBoundary_norm (R.curve ⟨0, bot_lt_top⟩).re) t) := by
      funext t
      change standardCirclePoint _ = standardCirclePoint _
      rw [R.start_eq_real]
    change halfPlaneDisk x ∈ range (fun t : PathTime =>
      boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) ↔ _
    rw [heq]
    exact hb
  simp only [side, hc]

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RaySideConnectivity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both sides of each compactified lifted ray are connected. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

theorem subset_complement (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    jordanInterior H ⊆ Metric.ball 0 1 \ range R.crosscut := by
  intro z hz
  refine ⟨(R.filling_subset hf).2 hz, ?_⟩
  intro hp
  have hfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hp
  have hi : z ∈ interior (jordanInterior H) := by
    simpa only [(jordanInterior_isOpen H).interior_eq] using hz
  exact Set.disjoint_left.mp disjoint_interior_frontier hi hfront

theorem component_in_or_out (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H)
    {V : Set ℂ} (hV : IsPreconnected V)
    (hsub : V ⊆ Metric.ball 0 1 \ range R.crosscut) :
    V ⊆ jordanInterior H ∨ V ⊆ (closure (jordanInterior H))ᶜ := by
  apply hV.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact disjoint_compl_right.mono_left subset_closure
  · intro z hz
    by_cases hin : z ∈ jordanInterior H
    · exact Or.inl hin
    · right
      intro hcl
      have hfront : z ∈ frontier (jordanInterior H) := by
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hcl, hin⟩
      rw [hf] at hfront
      rcases hfront with hp | ⟨t, rfl⟩
      · exact (hsub hz).2 hp
      · have hn : ‖boundaryClosingArc _ R.crosscut_start_norm t‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using (hsub hz).1
        rw [boundaryClosingArc_norm] at hn
        exact lt_irrefl _ hn

theorem exterior_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ)
    (hf : R.IsJordan H) :
    IsConnected (Metric.ball 0 1 \ closure (jordanInterior H)) := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hd, hcover, _, _⟩ :=
    hsep R.crosscut.toContinuousMap R.compactify_injective
      R.crosscut_start_norm (by
        change ‖R.compactify ⊤‖ = 1
        rw [R.compactify_top, norm_one])
      R.crosscut_interior
  have hJsub := subset_complement R H hf
  have hJUorV : jordanInterior H ⊆ U ∨ jordanInterior H ⊆ V := by
    apply (isConnected_jordanInterior H).isPreconnected.subset_or_subset hUo hVo hd
    exact fun z hz => hcover ▸ hJsub hz
  have hcase (A B : Set ℂ) (hAc : IsConnected A) (hBc : IsConnected B)
      (hAB : Disjoint A B) (hc : A ∪ B = Metric.ball 0 1 \ range R.crosscut)
      (hJA : jordanInterior H ⊆ A) :
      Metric.ball 0 1 \ closure (jordanInterior H) = B := by
    have hAsub : A ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_left
    have hBsub : B ⊆ Metric.ball 0 1 \ range R.crosscut := hc ▸ subset_union_right
    have hAJ : A ⊆ jordanInterior H := by
      rcases component_in_or_out R H hf hAc.isPreconnected hAsub with h | h
      · exact h
      · obtain ⟨z, hz⟩ := (isConnected_jordanInterior H).nonempty
        exact (h (hJA hz) (subset_closure hz)).elim
    have hBout : B ⊆ (closure (jordanInterior H))ᶜ := by
      rcases component_in_or_out R H hf hBc.isPreconnected hBsub with h | h
      · obtain ⟨z, hz⟩ := hBc.nonempty
        exact (Set.disjoint_left.mp hAB (hJA (h hz)) hz).elim
      · exact h
    apply Subset.antisymm
    · intro z hz
      have hn : z ∉ range R.crosscut := by
        intro hp
        exact hz.2 (frontier_subset_closure (hf ▸ Or.inl hp))
      have hu : z ∈ A ∪ B := hc ▸ ⟨hz.1, hn⟩
      rcases hu with hA | hB
      · exact (hz.2 (subset_closure (hAJ hA))).elim
      · exact hB
    · intro z hz
      exact ⟨(hBsub hz).1, hBout hz⟩
  rcases hJUorV with h | h
  · rw [hcase U V hUc hVc hd hcover h]
    exact hVc
  · rw [hcase V U hVc hUc hd.symm (union_comm U V ▸ hcover) h]
    exact hUc


theorem leftSide_connected (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (closure (jordanInterior H) \ range R.crosscut) := by
  apply (isConnected_jordanInterior H).subset_closure
  · intro z hz
    exact ⟨subset_closure hz, (R.subset_complement H hf hz).2⟩
  · exact sdiff_subset

theorem rightSide_connected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (hf : R.IsJordan H) :
    IsConnected (Metric.closedBall 0 1 \ closure (jordanInterior H)) := by
  apply (R.exterior_connected hsep H hf).subset_closure
  · exact sdiff_subset_sdiff_left Metric.ball_subset_closedBall
  · intro z hz
    have hh : z ∈ (closure (jordanInterior H))ᶜ ∩ closure (Metric.ball (0 : ℂ) 1) := by
      refine ⟨hz.2, ?_⟩
      simpa only [closure_ball _ one_ne_zero] using hz.1
    have hi := isClosed_closure.isOpen_compl.inter_closure hh
    change z ∈ closure (Metric.ball 0 1 ∩ (closure (jordanInterior H))ᶜ)
    simpa only [inter_comm] using hi

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VerticalRayAvoidance
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common angular strip bound makes all sufficiently far translates
miss each vertical segment to the real boundary. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem verticalCayleyPath_norm_le (x y : ℝ) (hy : 0 ≤ y) (t : PathTime) :
    ‖verticalCayleyPath x y hy t‖ ≤ 1 := halfPlaneDisk_norm_le (vertical_im_nonneg x y hy t)

theorem verticalCayleyPath_common_strip_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (Y : ℝ) :
    ∃ M : ℝ, ∀ x y : ℝ, ∀ hy : 0 ≤ y, y ≤ Y → ∀ γ : K, ∀ k : ℤ,
      ¬ Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) →
      |x - (k : ℝ)| ≤ M := by
  obtain ⟨M, hM⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  refine ⟨M, ?_⟩
  intro x y hy hyY γ k hh
  obtain ⟨z, ⟨s, hs⟩, ⟨t, ht⟩⟩ := Set.not_disjoint_iff.mp hh
  have he : verticalCayleyPath x y hy s =
      (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t := hs.trans ht.symm
  have hnonneg := vertical_im_nonneg x y hy s
  have htop : t < ⊤ := by
    by_contra hn
    have het : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
    rw [het, HalfPlaneRay.compactify_top] at he
    exact halfPlaneDisk_ne_one hnonneg he
  rw [HalfPlaneRay.compactify, dite_eq_left htop] at he
  have hc := halfPlaneDisk_injOn hnonneg
    ((translatedHalfPlaneRay γ.val (hKS γ.property) k).nonneg ⟨t, htop⟩) he
  have hdep : diskRayDepth γ.val ⟨t, htop⟩ = (s : ℝ) * y := by
    have hi := congrArg Complex.im hc
    simpa only [verticalCayleyPath, ContinuousMap.coe_mk, translatedHalfPlaneRay,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
      Complex.intCast_im, diskRayComplex_im] using hi.symm
  have hdle : diskRayDepth γ.val ⟨t, htop⟩ ≤ y := by
    rw [hdep]
    exact mul_le_of_le_one_left hy s.property.2
  have hre : x = diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ + (k : ℝ) := by
    have hr := congrArg Complex.re hc
    simpa [verticalCayleyPath, translatedHalfPlaneRay, diskRayComplex] using hr
  have hb := hM γ ⟨t, htop⟩ (hdle.trans hyY)
  have hsub : x - (k : ℝ) =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ := by linarith
  rwa [hsub]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FarRaySides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform eventual values of the translated side functions on bounded
rectangles of the half-plane. This gives the finite range of possible indices. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem side_eq_boundary_of_vertical_avoidance (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) (x y : ℝ) (hy : 0 ≤ y)
    (hmiss : Disjoint (range (verticalCayleyPath x y hy)) (range R.crosscut)) :
    (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hm (t : PathTime) : verticalCayleyPath x y hy t ∉ range R.crosscut :=
    Set.disjoint_left.mp hmiss (mem_range_self t)
  let f : PathTime → R.CutDomain := fun t =>
    ⟨verticalCayleyPath x y hy t, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using verticalCayleyPath_norm_le x y hy t), hm t⟩
  have hc : Continuous f := (verticalCayleyPath x y hy).continuous.subtype_mk _
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    (1 : PathTime) 0
  have h0 : halfPlaneDisk x ∉ range R.crosscut := by simpa only [verticalCayleyPath_zero] using hm 0
  have hb := R.side_boundary hH x h0
  have he' : (if halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)
      then false else true) = (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) := by
    simpa only [Function.comp_apply, side, f, verticalCayleyPath_zero, verticalCayleyPath_one] using he
  exact he'.trans hb

end HalfPlaneRay

theorem translated_sides_eventually_fixed
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ N : ℝ, 0 < N ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → ∀ _hy : 0 ≤ y, y ≤ Y →
      ∀ (k : ℤ) (H : ℂ ≃ₜ ℂ), (translatedHalfPlaneRay γ.val (hKS γ.property) k).IsJordan H →
      (N < (k : ℝ) → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∈ closure (jordanInterior H)) ∧
      ((k : ℝ) < -N → halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) ∉ closure (jordanInterior H)) := by
  obtain ⟨M, hM⟩ := verticalCayleyPath_common_strip_bound K hK hKS Y
  obtain ⟨A, hA⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  let N := |M| + |A| + X + 2
  refine ⟨N, by dsimp [N] <;> positivity, ?_⟩
  intro γ x y hx hy hyY k H hH
  have hzero : diskRayDepth γ.val ⟨0, bot_lt_top⟩ = 0 := by
    simp only [diskRayDepth, (hKS γ.property).2.1, Real.log_one, neg_zero]
  have ha := hA γ ⟨0, bot_lt_top⟩ (by simpa only [hzero] using hY)
  have hlo : -|A| ≤ diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ :=
    (abs_le.mp ha).1.trans' (neg_le_neg (le_abs_self A))
  have hhi : diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ ≤ |A| :=
    (abs_le.mp ha).2.trans (le_abs_self A)
  have hstart : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨0, bot_lt_top⟩ + (k : ℝ) := by
    simp [translatedHalfPlaneRay, diskRayComplex]
  have hside (hk : M < |x - (k : ℝ)|) := by
    have hmiss : Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) := by
      by_contra hn
      exact (not_le_of_gt hk) (hM x y hy hyY γ k hn)
    exact HalfPlaneRay.side_eq_boundary_of_vertical_avoidance _ hH x y hy hmiss
  constructor
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := neg_le_abs (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hle : x ≤ ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re := by
      rw [hstart]
      have hx' := (abs_le.mp hx).2
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_left hle] at hs
    by_contra hn
    simp only [ite_eq_right hn] at hs
    cases hs
  · intro hk
    have hlarge : M < |x - (k : ℝ)| := by
      have hab := le_abs_self (x - (k : ℝ))
      have hm := le_abs_self M
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg A]
    have hs := hside hlarge
    have hlt : ((translatedHalfPlaneRay γ.val (hKS γ.property) k).curve ⟨0, bot_lt_top⟩).re < x := by
      rw [hstart]
      have hx' := (abs_le.mp hx).1
      dsimp [N] at hk
      linarith [abs_nonneg M]
    simp only [ite_eq_right (not_le_of_gt hlt)] at hs
    intro hin
    simp only [ite_eq_left hin] at hs
    cases hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricRayIndex
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual greatest-translate index. Compact strip bounds prove that
the defining set is nonempty and bounded above, uniformly over the arc law. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem rayJordan_spec (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    (translatedHalfPlaneRay γ hγ k).IsJordan (rayJordan hsch γ hγ k) :=
  Classical.choose_spec ((translatedHalfPlaneRay γ hγ k).exists_jordan hsch)

theorem compact_ray_indices_bounded (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ B : ℤ, 0 < B ∧ ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      (-B ∈ rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) ∧
      B ∈ upperBounds (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  obtain ⟨N, hN, hfixed⟩ := translated_sides_eventually_fixed K hK hKS X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hBpos : 0 < B := by exact_mod_cast hN.trans hB
  refine ⟨B, hBpos, ?_⟩
  intro γ x y hx hy hyY
  have hneg : ((-B : ℤ) : ℝ) < -N := by rw [Int.cast_neg]; linarith
  constructor
  · exact (hfixed γ x y hx hy hyY (-B) (rayJordan hsch γ.val (hKS γ.property) (-B))
      (rayJordan_spec hsch γ.val (hKS γ.property) (-B))).2 hneg
  · intro k hk
    by_contra hnot
    have hBk : B < k := lt_of_not_ge hnot
    have hNk : N < (k : ℝ) := hB.trans (by exact_mod_cast hBk)
    exact hk ((hfixed γ x y hx hy hyY k (rayJordan hsch γ.val (hKS γ.property) k)
      (rayJordan_spec hsch γ.val (hKS γ.property) k)).1 hNk)

theorem rayRightIndices_nonempty_bddAbove (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    (rayRightIndices hsch γ hγ z).Nonempty ∧ BddAbove (rayRightIndices hsch γ hγ z) := by
  obtain ⟨B, _, hb⟩ := compact_ray_indices_bounded hsch {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) |z.re| z.im (abs_nonneg _) hz
  have h := hb ⟨γ, mem_singleton γ⟩ z.re z.im le_rfl hz le_rfl
  have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  simpa only [he] using And.intro (show (rayRightIndices hsch γ hγ
    ((z.re : ℂ) + (z.im : ℂ) * Complex.I)).Nonempty from ⟨-B, h.1⟩)
    (show BddAbove (rayRightIndices hsch γ hγ ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) from ⟨B, h.2⟩)

theorem geometricRayIndex_isGreatest (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    IsGreatest (rayRightIndices hsch γ hγ z) (geometricRayIndex hsch γ hγ z) := by
  obtain ⟨hne, hbdd⟩ := rayRightIndices_nonempty_bddAbove hsch γ hγ z hz
  exact ⟨Int.csSup_mem hne hbdd, fun _ hk => le_csSup hbdd hk⟩

theorem compact_geometricRayIndex_bound (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ∃ M : ℝ, ∀ (γ : K) (x y : ℝ), |x| ≤ X → 0 ≤ y → y ≤ Y →
      |(geometricRayIndex hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I) : ℝ)| ≤ M := by
  obtain ⟨B, _, hB⟩ := compact_ray_indices_bounded hsch K hK hKS X Y hX hY
  refine ⟨(B : ℝ), ?_⟩
  intro γ x y hx hy hyY
  obtain ⟨hlow, hupp⟩ := hB γ x y hx hy hyY
  have hnon : (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)).Nonempty :=
    ⟨-B, hlow⟩
  have hbdd : BddAbove (rayRightIndices hsch γ.val (hKS γ.property) ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    ⟨B, hupp⟩
  have hsup := Int.csSup_mem hnon hbdd
  have hl := le_csSup hbdd hlow
  have hu := hupp hsup
  apply abs_le.mpr
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GeometricIndexBoundary
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Calibration of the greatest-translate index on the real boundary.
The value is the floor of the horizontal coordinate minus the arc start. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem HalfPlaneRay.boundary_hit_iff (R : HalfPlaneRay) (x : ℝ) :
    halfPlaneDisk x ∈ range R.crosscut ↔ x = (R.curve ⟨0, bot_lt_top⟩).re := by
  constructor
  · rintro ⟨t, ht⟩
    have htlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk x at ht
      rw [R.compactify_top] at ht
      exact cayleyBoundary_ne_one x ht.symm
    change R.compactify t = halfPlaneDisk x at ht
    rw [HalfPlaneRay.compactify, dite_eq_left htlt] at ht
    have hc := halfPlaneDisk_injOn (R.nonneg ⟨t, htlt⟩) (by simp) ht
    have hzero : t = 0 := by
      by_contra hn
      have hp := R.positive ⟨t, htlt⟩ (lt_of_le_of_ne bot_le (Ne.symm hn))
      have hi := congrArg Complex.im hc
      simp only [Complex.ofReal_im] at hi
      exact (ne_of_gt hp) hi
    subst t
    exact (congrArg Complex.re hc).symm
  · intro hx
    refine ⟨0, ?_⟩
    change R.compactify 0 = halfPlaneDisk x
    rw [R.start_eq_real, hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TranslatedRayOrder
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The side of one translated ray relative to another is fixed by their
starting order on the real boundary. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem translated_curve_avoids_crosscut (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉
      range (translatedHalfPlaneRay γ hγ k).crosscut := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  rintro ⟨s, hs⟩
  have hst : s < ⊤ := by
    by_contra hn
    have he : s = ⊤ := top_le_iff.mp (not_lt.mp hn)
    subst s
    change R.compactify ⊤ = halfPlaneDisk (S.curve t) at hs
    rw [R.compactify_top] at hs
    exact halfPlaneDisk_ne_one (S.nonneg t) hs.symm
  change R.compactify s = halfPlaneDisk (S.curve t) at hs
  rw [HalfPlaneRay.compactify, dite_eq_left hst] at hs
  have hc := halfPlaneDisk_injOn (R.nonneg ⟨s, hst⟩) (S.nonneg t) hs
  exact hkl ((translatedHalfPlaneRay_meet_iff γ hγ k l ⟨s, hst⟩ t).mp hc).1

theorem translated_ray_side_value (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k ≠ l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    (if halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H)
      then false else true) = if l ≤ k then false else true := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let f : DiskRayTime → R.CutDomain := fun u => ⟨halfPlaneDisk (S.curve u),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (S.nonneg u)),
    translated_curve_avoids_crosscut γ hγ hkl u⟩
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    exact continuousOn_halfPlaneDisk.comp_continuous S.curve.continuous S.nonneg
  let : PreconnectedSpace DiskRayTime := Subtype.preconnectedSpace
    (isPreconnected_Iio (a := (⊤ : PathTime)))
  have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
    t (⟨0, bot_lt_top⟩ : DiskRayTime)
  have hs0 : S.curve ⟨0, bot_lt_top⟩ = ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using S.start
  have hm : halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∉ range R.crosscut := by
    rw [← hs0]
    exact translated_curve_avoids_crosscut γ hγ hkl ⟨0, bot_lt_top⟩
  have hb := R.side_boundary hH (S.curve ⟨0, bot_lt_top⟩).re hm
  have he' : (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk ((S.curve ⟨0, bot_lt_top⟩).re : ℂ) ∈ closure (jordanInterior H) then false else true) := by
    change (if halfPlaneDisk (S.curve t) ∈ closure (jordanInterior H) then false else true) =
      (if halfPlaneDisk (S.curve ⟨0, bot_lt_top⟩) ∈ closure (jordanInterior H) then false else true) at he
    rw [hs0] at he
    exact he
  have hle : (S.curve ⟨0, bot_lt_top⟩).re ≤ (R.curve ⟨0, bot_lt_top⟩).re ↔ l ≤ k := by
    simp only [S, R, translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
      diskRayComplex, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.intCast_re,
      add_le_add_iff_left, Int.cast_le]
  exact he'.trans (hb.trans (by simp only [hle]))

theorem earlier_ray_left (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hlk : l < k) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∈ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hlk.ne' H hH t
  rw [ite_eq_left hlk.le] at h
  by_contra hi
  rw [ite_eq_right hi] at h
  cases h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TranslatedSideNesting
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right components of integer translates form a decreasing family.
This is derived from crosscut separation and the order of the actual starts. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem HalfPlaneRay.boundary_right (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ}
    (hH : R.IsJordan H) {x : ℝ} (hx : (R.curve ⟨0, bot_lt_top⟩).re < x) :
    halfPlaneDisk x ∉ closure (jordanInterior H) := by
  have hm : halfPlaneDisk x ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt hx
  have hb := R.side_boundary hH x hm
  change (if halfPlaneDisk x ∈ closure (jordanInterior H) then false else true) = _ at hb
  rw [ite_eq_right (not_le_of_gt hx)] at hb
  intro hi
  rw [ite_eq_left hi] at hb
  cases hb

 theorem earlier_crosscut_in_later_filling (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) {k l : ℤ} (hkl : k < l)
    (H : ℂ ≃ₜ ℂ) (hH : (translatedHalfPlaneRay γ hγ l).IsJordan H) :
    range (translatedHalfPlaneRay γ hγ k).crosscut ⊆ closure (jordanInterior H) := by
  rintro z ⟨t, rfl⟩
  by_cases ht : t < ⊤
  · change (translatedHalfPlaneRay γ hγ k).compactify t ∈ _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
    exact earlier_ray_left γ hγ hkl H hH ⟨t, ht⟩
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have hf : (1 : ℂ) ∈ frontier (jordanInterior H) := by
      rw [hH]
      left
      exact ⟨⊤, (translatedHalfPlaneRay γ hγ l).compactify_top⟩
    change (translatedHalfPlaneRay γ hγ k).compactify ⊤ ∈ _
    rw [HalfPlaneRay.compactify_top]
    exact frontier_subset_closure hf

 theorem translated_rightSide_antitone (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (Hk Hl : ℂ ≃ₜ ℂ)
    (hk : (translatedHalfPlaneRay γ hγ k).IsJordan Hk)
    (hl : (translatedHalfPlaneRay γ hγ l).IsJordan Hl) :
    Metric.closedBall 0 1 \ closure (jordanInterior Hl) ⊆
      Metric.closedBall 0 1 \ closure (jordanInterior Hk) := by
  let R := translatedHalfPlaneRay γ hγ k
  let S := translatedHalfPlaneRay γ hγ l
  let A := Metric.closedBall (0 : ℂ) 1 \ closure (jordanInterior Hl)
  have havoid : ∀ z : A, z.val ∉ range R.crosscut := by
    intro z hz
    exact z.property.2 (earlier_crosscut_in_later_filling γ hγ hkl Hl hl hz)
  let f : A → R.CutDomain := fun z => ⟨z.val, z.property.1, havoid z⟩
  have hc : Continuous f := continuous_subtype_val.subtype_mk _
  let : PreconnectedSpace A := Subtype.preconnectedSpace
    (S.rightSide_connected hsep Hl hl).isPreconnected
  let x : ℝ := max (R.curve ⟨0, bot_lt_top⟩).re (S.curve ⟨0, bot_lt_top⟩).re + 1
  have hkx : (R.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hlx : (S.curve ⟨0, bot_lt_top⟩).re < x := by
    exact lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
  let z₀ : A := ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
    (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), S.boundary_right hl hlx⟩
  intro z hz
  let w : A := ⟨z, hz⟩
  have he := ((R.isLocallyConstant_side hk).comp_continuous hc).apply_eq_of_preconnectedSpace w z₀
  have he' : (if z ∈ closure (jordanInterior Hk) then false else true) = true := by
    simpa only [Function.comp_apply, HalfPlaneRay.side, f, w, z₀,
      ite_eq_right (R.boundary_right hk hkx)] using he
  refine ⟨hz.1, ?_⟩
  intro hi
  rw [ite_eq_left hi] at he'
  cases he'

 theorem rayRightIndices_downward (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im)
    {k l : ℤ} (hkl : k ≤ l) (hl : l ∈ rayRightIndices hsch γ hγ z) :
    k ∈ rayRightIndices hsch γ hγ z := by
  rcases hkl.eq_or_lt with rfl | hlt
  · exact hl
  · exact (translated_rightSide_antitone hsep γ hγ hlt
      (rayJordan hsch γ hγ k) (rayJordan hsch γ hγ l)
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ l)
      ⟨Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz), hl⟩).2

 theorem mem_rayRightIndices_iff_le (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    k ∈ rayRightIndices hsch γ hγ z ↔ k ≤ geometricRayIndex hsch γ hγ z := by
  have hg := geometricRayIndex_isGreatest hsch γ hγ z hz
  exact ⟨fun hk => hg.2 hk, fun hk => rayRightIndices_downward hsch hsep γ hγ z hz hk hg.1⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RayProjection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic half-plane projection sends every integer translate
back to the original terminal arc. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem continuous_diskRayProjection : Continuous diskRayProjection := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im.neg)
  · exact continuous_subtype_val.comp
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.comp
        ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re))

theorem diskRayProjection_norm (z : ℂ) : ‖diskRayProjection z‖ = Real.exp (-z.im) := by
  rw [diskRayProjection, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hn : ‖standardCirclePoint (z.re : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  rw [hn, mul_one]

theorem diskRayProjection_argument (z : ℂ) :
    normalizedArgument (diskRayProjection z) = (z.re : UnitAddCircle) := by
  rw [diskRayProjection, normalizedArgument,
    Complex.arg_real_mul _ (Real.exp_pos _)]
  exact normalizedArgument_standardCirclePoint _

theorem diskRayProjection_translated (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t) = γ t.val := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    change Real.exp (-((diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)).im)) = _
    rw [Complex.add_im, Complex.intCast_im, add_zero, diskRayComplex_im,
      diskRayDepth, neg_neg, Real.exp_log (norm_pos_iff.mpr (diskRay_nonzero γ hγ.1 hγ.2.2.1 t))]
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection ((translatedHalfPlaneRay γ hγ k).curve t)) = _
    rw [diskRayProjection_argument]
    have hr : ((translatedHalfPlaneRay γ hγ k).curve t).re =
        diskRayAngle γ hγ.1 hγ.2.2.1 t + (k : ℝ) := by
      simp only [translatedHalfPlaneRay, ContinuousMap.coe_mk, Complex.add_re,
        Complex.intCast_re, diskRayComplex, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hr]
    have hk : ((k : ℝ) : UnitAddCircle) = 0 :=
      (addCircle_eq_iff_exists_int 1 (k : ℝ) 0).mpr ⟨k, by simp⟩
    rw [AddCircle.coe_add, hk, add_zero]
    exact diskRayAngle_projects γ hγ.1 hγ.2.2.1 t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RayIndexCrossings
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every integer between two index values forces a distinct intersection.
Injectivity of the projected test path makes these physical intersections distinct. -/

open Set Function Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem HalfPlaneRay.cayley_mem_crosscut_iff (R : HalfPlaneRay) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∈ range R.crosscut ↔ z ∈ range R.curve := by
  constructor
  · rintro ⟨t, ht⟩
    have hlt : t < ⊤ := by
      by_contra hn
      have he : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
      subst t
      change R.compactify ⊤ = halfPlaneDisk z at ht
      rw [R.compactify_top] at ht
      exact halfPlaneDisk_ne_one hz ht.symm
    refine ⟨⟨t, hlt⟩, ?_⟩
    change R.compactify t = halfPlaneDisk z at ht
    rw [HalfPlaneRay.compactify, dite_eq_left hlt] at ht
    exact halfPlaneDisk_injOn (R.nonneg _) hz ht
  · rintro ⟨t, rfl⟩
    exact ⟨t.val, by change R.compactify t.val = _; rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩

theorem translated_ray_hit_between_indices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (k : ℤ) (h0 : geometricRayIndex hsch γ hγ (δ 0) < k)
    (h1 : k ≤ geometricRayIndex hsch γ hγ (δ 1)) :
    ∃ s : PathTime, ∃ t : DiskRayTime, δ s = (translatedHalfPlaneRay γ hγ k).curve t := by
  let R := translatedHalfPlaneRay γ hγ k
  let H := rayJordan hsch γ hγ k
  have ha : halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) := by
    by_contra hn
    have hm : k ∈ rayRightIndices hsch γ hγ (δ 0) := hn
    exact (not_le_of_gt h0) ((mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 0) (hδ 0) k).mp hm)
  have hb : halfPlaneDisk (δ 1) ∉ closure (jordanInterior H) :=
    (mem_rayRightIndices_iff_le hsch hsep γ hγ (δ 1) (hδ 1) k).mpr h1
  by_contra hn
  have hmiss : ∀ s, halfPlaneDisk (δ s) ∉ range R.crosscut := by
    intro s hs
    obtain ⟨t, ht⟩ := (R.cayley_mem_crosscut_iff (hδ s)).mp hs
    exact hn ⟨s, t, ht.symm⟩
  let f : PathTime → R.CutDomain := fun s => ⟨halfPlaneDisk (δ s),
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le (hδ s)), hmiss s⟩
  have hc : Continuous f := (continuousOn_halfPlaneDisk.comp_continuous δ.continuous hδ).subtype_mk _
  have he := ((R.isLocallyConstant_side (rayJordan_spec hsch γ hγ k)).comp_continuous hc).apply_eq_of_preconnectedSpace
    (0 : PathTime) 1
  change (if halfPlaneDisk (δ 0) ∈ closure (jordanInterior H) then false else true) =
    (if halfPlaneDisk (δ 1) ∈ closure (jordanInterior H) then false else true) at he
  rw [ite_eq_left ha, ite_eq_right hb] at he
  cases he

theorem geometric_index_interval_count (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ((Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0))
      (geometricRayIndex hsch γ hγ (δ 1))).card : ℝ≥0∞) ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  let F := Finset.Ioc (geometricRayIndex hsch γ hγ (δ 0)) (geometricRayIndex hsch γ hγ (δ 1))
  have hex : ∀ k : F, ∃ s : PathTime, ∃ t : DiskRayTime,
      δ s = (translatedHalfPlaneRay γ hγ k.val).curve t := by
    intro k
    have hk := Finset.mem_Ioc.mp k.property
    exact translated_ray_hit_between_indices hsch hsep γ hγ δ hδ k.val hk.1 hk.2
  choose s t ht using hex
  let x : F → ℂ := fun k => diskRayProjection (δ (s k))
  have hx (k : F) : x k ∈ range γ ∩ diskRayProjection '' range δ := by
    refine ⟨⟨(t k).val, ?_⟩, δ (s k), mem_range_self _, rfl⟩
    dsimp [x]
    rw [ht k, diskRayProjection_translated]
  have hxi : Injective x := by
    intro k l hkl
    have hs : s k = s l := hinj hkl
    have hh : (translatedHalfPlaneRay γ hγ k.val).curve (t k) =
        (translatedHalfPlaneRay γ hγ l.val).curve (t l) := (ht k).symm.trans (hs ▸ ht l)
    exact Subtype.ext ((translatedHalfPlaneRay_meet_iff γ hγ k.val l.val (t k) (t l)).mp hh).1
  calc
    (F.card : ℝ≥0∞) = ∑' k : F, if x k ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0 := by
      simp only [hx, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_coe, nsmul_eq_mul, mul_one]
    _ ≤ pathImageCount (diskRayProjection '' range δ) γ :=
      ENNReal.tsum_comp_le_tsum_of_injective hxi
        (fun z => if z ∈ range γ ∩ diskRayProjection '' range δ then (1 : ℝ≥0∞) else 0)

theorem geometric_index_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |(geometricRayIndex hsch γ hγ (δ 1) : ℝ) -
      (geometricRayIndex hsch γ hγ (δ 0) : ℝ)| ≤
      pathImageCount (diskRayProjection '' range δ) γ := by
  have hforward (ε : C(PathTime, ℂ)) (hε : ∀ t, 0 ≤ (ε t).im)
      (hi : Injective (diskRayProjection ∘ ε))
      (hle : geometricRayIndex hsch γ hγ (ε 0) ≤ geometricRayIndex hsch γ hγ (ε 1)) :
      ENNReal.ofReal ((geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ)) ≤
        pathImageCount (diskRayProjection '' range ε) γ := by
    have hcard := Int.card_Ioc_of_le _ _ hle
    have hr : ((Finset.Ioc (geometricRayIndex hsch γ hγ (ε 0))
        (geometricRayIndex hsch γ hγ (ε 1))).card : ℝ) =
        (geometricRayIndex hsch γ hγ (ε 1) : ℝ) -
        (geometricRayIndex hsch γ hγ (ε 0) : ℝ) := by exact_mod_cast hcard
    rw [← hr, ENNReal.ofReal_natCast]
    exact geometric_index_interval_count hsch hsep γ hγ ε hε hi
  by_cases hle : geometricRayIndex hsch γ hγ (δ 0) ≤ geometricRayIndex hsch γ hγ (δ 1)
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]
    exact hforward δ hδ hinj hle
  · let ε : C(PathTime, ℂ) := ⟨δ ∘ unitInterval.symm, δ.continuous.comp unitInterval.continuous_symm⟩
    have hε0 : ε 0 = δ 1 := congrArg δ unitInterval.symm_zero
    have hε1 : ε 1 = δ 0 := congrArg δ unitInterval.symm_one
    have hrange : range ε = range δ := unitInterval.symmHomeomorph.surjective.range_comp δ
    have hi : Injective (diskRayProjection ∘ ε) := hinj.comp unitInterval.symmHomeomorph.injective
    have hh := hforward ε (fun t => hδ _) hi (by rw [hε0, hε1]; exact le_of_not_ge hle)
    rw [hε0, hε1, hrange] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hle))), neg_sub]
    exact hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RayFamilyMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dependence of the compactified rays on the actual arc sample.
No measurable choice of Schoenflies homeomorphisms is used. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

variable (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)

theorem continuous_initialArcAngles_family (c : PathTime) (hc : c < ⊤) :
    Continuous (fun γ : K => initialArcAngles puncturedArgument γ.val
      (hKS γ.property).1 (hKS γ.property).2.2.1 c hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply puncturedArgument.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_snd.mul continuous_const))

theorem measurable_diskRayAngle_family (t : DiskRayTime) :
    Measurable (fun γ : K => diskRayAngle γ.val (hKS γ.property).1
      (hKS γ.property).2.2.1 t) := by
  have hs : Measurable (fun γ : K => circleRepresentative (normalizedArgument (γ.val 0))) :=
    measurable_circleRepresentative_dup1.comp (measurable_normalizedArgument.comp
      ((continuous_eval_const 0).comp continuous_subtype_val).measurable)
  have hi := continuous_circlePathIncrement.comp (continuous_initialArcAngles_family K hKS t.val t.property)
  convert hs.add hi.measurable using 1
  all_goals try with_reducible_and_instances rfl
  funext γ
  exact diskRayAngle_eq_increment _ _ _ t

theorem measurable_translatedRay_family (k : ℤ) (t : DiskRayTime) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).curve t) := by
  have ha := measurable_diskRayAngle_family K hKS t
  have hd : Measurable (fun γ : K => diskRayDepth γ.val t) :=
    (((continuous_eval_const t.val).comp continuous_subtype_val).measurable.norm.log).neg
  exact ((Complex.continuous_ofReal.measurable.comp ha).add
    ((Complex.continuous_ofReal.measurable.comp hd).mul_const Complex.I)).add_const (k : ℂ)

theorem measurable_translatedCrosscut_family (k : ℤ) :
    Measurable (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  by_cases ht : t < ⊤
  · have hc : Measurable halfPlaneDisk := by
      unfold halfPlaneDisk
      fun_prop
    have hm := hc.comp (measurable_translatedRay_family K hKS k ⟨t, ht⟩)
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext γ
    change (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t = halfPlaneDisk _
    rw [HalfPlaneRay.compactify, dite_eq_left ht]
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    have heq : (fun γ : K => (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut.toContinuousMap ⊤) =
        fun _ => (1 : ℂ) := by
      funext γ
      exact HalfPlaneRay.compactify_top _
    rw [heq]
    exact measurable_const

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CutPathComponents
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A closed-disk crosscut complement is locally path connected. Thus the
connected sides already proved are its actual path components. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.HalfPlaneRay

 theorem cutDomain_locallyPathConnected (R : HalfPlaneRay) : LocallyPathConnectedSpace R.CutDomain := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrmiss⟩ := Metric.isOpen_iff.mp
    (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl x.val x.property.2
  let d := min ε r
  have hd : 0 < d := lt_min hε hr
  refine ⟨Metric.ball x d, Metric.ball_mem_nhds _ hd, ?_, ?_⟩
  · apply Topology.IsInducing.subtypeVal.isPathConnected_iff.mpr
    have he : Subtype.val '' Metric.ball x d =
        Metric.ball x.val d ∩ Metric.closedBall (0 : ℂ) 1 := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨hw, w.property.1⟩
      · intro hz
        have hzr : z ∈ Metric.ball x.val r :=
          (Metric.ball_subset_ball (min_le_right ε r)) hz.1
        have hm : z ∉ range R.crosscut := hrmiss hzr
        exact ⟨⟨z, hz.2, hm⟩, hz.1, rfl⟩
    rw [he]
    exact ((convex_ball x.val d).inter (convex_closedBall (0 : ℂ) 1)).isPathConnected
      ⟨x.val, Metric.mem_ball_self hd, x.property.1⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hεU

 theorem side_fiber_preconnected (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (b : Bool) :
    IsPreconnected {z : R.CutDomain | R.side H z = b} := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  cases b with
  | false =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = false} =
        closure (jordanInterior H) \ range R.crosscut := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨?_, w.property.2⟩
        by_contra hn
        change (if w.val ∈ closure (jordanInterior H) then false else true) = false at hw
        rw [ite_eq_right hn] at hw
        cases hw
      · intro hz
        refine ⟨⟨z, (R.filling_subset hH).1 hz.1, hz.2⟩, ?_, rfl⟩
        exact ite_eq_left hz.1
    rw [he]
    exact (R.leftSide_connected H hH).isPreconnected
  | true =>
    have he : Subtype.val '' {z : R.CutDomain | R.side H z = true} =
        Metric.closedBall 0 1 \ closure (jordanInterior H) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.property.1, ?_⟩
        intro hi
        change (if w.val ∈ closure (jordanInterior H) then false else true) = true at hw
        rw [ite_eq_left hi] at hw
        cases hw
      · intro hz
        have hm : z ∉ range R.crosscut := fun hp => hz.2
          (frontier_subset_closure (hH ▸ Or.inl hp))
        refine ⟨⟨z, hz.1, hm⟩, ?_, rfl⟩
        exact ite_eq_right hz.2
    rw [he]
    exact (R.rightSide_connected hsep H hH).isPreconnected

 theorem side_eq_iff_joined (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ Joined x y := by
  let : LocallyPathConnectedSpace R.CutDomain := R.cutDomain_locallyPathConnected
  constructor
  · intro he
    have hc : IsConnected {z : R.CutDomain | R.side H z = R.side H x} :=
      ⟨⟨x, rfl⟩, R.side_fiber_preconnected hsep hH _⟩
    have hp := ((R.isLocallyConstant_side hH).isOpen_fiber _).isConnected_iff_isPathConnected.mp hc
    exact (hp.joinedIn x rfl y he.symm).joined
  · intro h
    have hc := h.somePath.continuous
    have he := ((R.isLocallyConstant_side hH).comp_continuous hc).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    simpa only [Function.comp_apply, Path.source, Path.target] using he

end CircleDomainRigidity.HalfPlaneRay

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutPathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Side membership is characterized by a path avoiding the crosscut to
the corresponding explicit real-boundary point. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

theorem side_eq_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (x y : R.CutDomain) :
    R.side H x = R.side H y ↔ DiskAvoidingPath R.crosscut.toContinuousMap x.val y.val := by
  constructor
  · intro h
    have hj := (R.side_eq_iff_joined hsep hH x y).mp h
    let p := hj.somePath
    refine ⟨⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩, ?_, ?_, ?_⟩
    · exact congrArg Subtype.val p.source
    · exact congrArg Subtype.val p.target
    · exact fun t => (p t).property
  · rintro ⟨δ, h0, h1, hδ⟩
    let f : PathTime → R.CutDomain := fun t => ⟨δ t, hδ t⟩
    have hf : Continuous f := δ.continuous.subtype_mk _
    have he := ((R.isLocallyConstant_side hH).comp_continuous hf).apply_eq_of_preconnectedSpace
      (0 : PathTime) 1
    change (if δ 0 ∈ closure (jordanInterior H) then false else true) =
      (if δ 1 ∈ closure (jordanInterior H) then false else true) at he
    rw [h0, h1] at he
    exact he

theorem right_iff_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∉ closure (jordanInterior H) ↔ DiskAvoidingPath R.crosscut.toContinuousMap z
      (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re + 1
  have ha : (R.curve ⟨0, bot_lt_top⟩).re < a := lt_add_one _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_gt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = true := by
    exact ite_eq_right (R.boundary_right hH ha)
  constructor
  · intro hn
    have hm : z ∉ range R.crosscut := fun hp => hn (frontier_subset_closure (hH ▸ Or.inl hp))
    apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
    exact (ite_eq_right hn).trans hy.symm
  · rintro ⟨δ, h0, h1, hδ⟩
    have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
    have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
    rw [hy] at he
    intro hi
    change (if z ∈ closure (jordanInterior H) then false else true) = true at he
    rw [ite_eq_left hi] at he
    cases he

theorem left_iff_hit_or_avoidingPath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    z ∈ closure (jordanInterior H) ↔ z ∈ range R.crosscut ∨
      DiskAvoidingPath R.crosscut.toContinuousMap z
        (halfPlaneDisk (((R.curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) := by
  let a := (R.curve ⟨0, bot_lt_top⟩).re - 1
  have ha : a < (R.curve ⟨0, bot_lt_top⟩).re := sub_one_lt _
  have hmiss : halfPlaneDisk a ∉ range R.crosscut := by
    rw [R.boundary_hit_iff]
    exact ne_of_lt ha
  let y : R.CutDomain := ⟨halfPlaneDisk a,
    Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (cayleyBoundary_norm a).le), hmiss⟩
  have hy : R.side H y = false := by
    have hb := R.side_boundary hH a hmiss
    exact hb.trans (ite_eq_left ha.le)
  constructor
  · intro hi
    by_cases hm : z ∈ range R.crosscut
    · exact Or.inl hm
    · right
      apply (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mp
      exact (ite_eq_left hi).trans hy.symm
  · rintro (hm | hp)
    · exact frontier_subset_closure (hH ▸ Or.inl hm)
    · obtain ⟨δ, h0, h1, hδ⟩ := hp
      have hm : z ∉ range R.crosscut := h0 ▸ (hδ 0).2
      have he := (R.side_eq_iff_avoidingPath hsep hH ⟨z, hz, hm⟩ y).mpr ⟨δ, h0, h1, hδ⟩
      rw [hy] at he
      by_contra hi
      change (if z ∈ closure (jordanInterior H) then false else true) = false at he
      rw [ite_eq_right hi] at he
      cases he

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableRaySides
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both sides have analytic path descriptions, so their membership sets
are Borel by Suslin's theorem. This avoids a measurable Schoenflies choice. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem isClosed_pathPairMeet :
    IsClosed {p : C(PathTime, ℂ) × C(PathTime, ℂ) | ¬ Disjoint (range p.1) (range p.2)} := by
  let E : Set ((C(PathTime, ℂ) × C(PathTime, ℂ)) × (PathTime × PathTime)) :=
    {p | p.1.1 p.2.1 = p.1.2 p.2.2}
  have hE : IsClosed E := isClosed_eq
    (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.fst))
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd))
  have he : Prod.fst '' E = {p : C(PathTime, ℂ) × C(PathTime, ℂ) |
      ¬ Disjoint (range p.1) (range p.2)} := by
    ext p
    constructor
    · rintro ⟨⟨_, s, t⟩, h, rfl⟩ hd
      exact Set.disjoint_left.mp hd (mem_range_self s) (h ▸ mem_range_self t)
    · intro h
      obtain ⟨z, hz, hw⟩ := Set.not_disjoint_iff.mp h
      obtain ⟨s, hs⟩ := hz
      obtain ⟨t, ht⟩ := hw
      exact ⟨(p, s, t), hs.trans ht.symm, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace E hE

 theorem analyticSet_diskAvoidingPath {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (p : X → C(PathTime, ℂ)) (hp : Measurable p)
    (z w : X → ℂ) (hz : Measurable z) (hw : Measurable w) :
    AnalyticSet {x | DiskAvoidingPath (p x) (z x) (w x)} := by
  let E : Set (X × C(PathTime, ℂ)) := {q |
    q.2 0 = z q.1 ∧ q.2 1 = w q.1 ∧
      (∀ t, q.2 t ∈ Metric.closedBall 0 1) ∧ Disjoint (range (p q.1)) (range q.2)}
  have hball : IsClosed {δ : C(PathTime, ℂ) | ∀ t, δ t ∈ Metric.closedBall 0 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => Metric.isClosed_closedBall.preimage (continuous_eval_const t)
  have hE : MeasurableSet E := by
    have hmiss : MeasurableSet {q : X × C(PathTime, ℂ) |
        Disjoint (range (p q.1)) (range q.2)} := by
      convert (isClosed_pathPairMeet.measurableSet.compl.preimage
        ((hp.comp measurable_fst).prodMk measurable_snd)) using 1
      all_goals try with_reducible_and_instances rfl
      ext q
      change Disjoint (range (p q.1)) (range q.2) ↔ ¬¬ Disjoint (range (p q.1)) (range q.2)
      exact not_not.symm
    exact (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      (hz.comp measurable_fst)).inter
      ((measurableSet_eq_fun ((continuous_eval_const 1).measurable.comp measurable_snd)
        (hw.comp measurable_fst)).inter
        ((hball.measurableSet.preimage measurable_snd).inter hmiss))
  have he : Prod.fst '' E = {x | DiskAvoidingPath (p x) (z x) (w x)} := by
    ext x
    constructor
    · rintro ⟨⟨x, δ⟩, h, rfl⟩
      refine ⟨δ, h.1, h.2.1, fun t => ⟨h.2.2.1 t, ?_⟩⟩
      intro ht
      exact Set.disjoint_left.mp h.2.2.2 ht (mem_range_self t)
    · rintro ⟨δ, h0, h1, hδ⟩
      refine ⟨(x, δ), ⟨h0, h1, fun t => (hδ t).1, ?_⟩, rfl⟩
      apply Set.disjoint_left.mpr
      rintro u hu ⟨t, rfl⟩
      exact (hδ t).2 hu
  rw [← he]
  exact hE.analyticSet.image_of_continuous continuous_fst

 theorem measurableSet_rayRightFamily {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hsep : UnitDiskCrosscutSeparation)
    (R : X → HalfPlaneRay) (H : X → ℂ ≃ₜ ℂ) (hH : ∀ x, (R x).IsJordan (H x))
    (hp : Measurable (fun x => (R x).crosscut.toContinuousMap))
    (ha : Measurable (fun x => ((R x).curve ⟨0, bot_lt_top⟩).re))
    (z : X → ℂ) (hz : Measurable z) (hzd : ∀ x, z x ∈ Metric.closedBall 0 1) :
    MeasurableSet {x | z x ∉ closure (jordanInterior (H x))} := by
  have hM : Measurable halfPlaneDisk := by unfold halfPlaneDisk; fun_prop
  have hplus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.add_const 1))
  have hminus : Measurable (fun x => halfPlaneDisk
      ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ)) :=
    hM.comp (Complex.continuous_ofReal.measurable.comp (ha.sub_const 1))
  have hright : AnalyticSet {x | z x ∉ closure (jordanInterior (H x))} := by
    have he : {x | z x ∉ closure (jordanInterior (H x))} =
        {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
          (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ))} := by
      ext x
      exact (R x).right_iff_avoidingPath hsep (hH x) (hzd x)
    rw [he]
    exact analyticSet_diskAvoidingPath _ hp z _ hz hplus
  apply hright.measurableSet_of_compl
  have hhit : MeasurableSet {x | z x ∈ range (R x).crosscut} :=
    isClosed_pathHitSet.measurableSet.preimage (hp.prodMk hz)
  have hleft := analyticSet_diskAvoidingPath _ hp z _ hz hminus
  have he : {x | z x ∉ closure (jordanInterior (H x))}ᶜ =
      {x | z x ∈ range (R x).crosscut} ∪
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))} := by
    ext x
    simpa only [mem_compl_iff, mem_ofPred_eq, not_not, mem_union] using
      (R x).left_iff_hit_or_avoidingPath hsep (hH x) (hzd x)
  rw [he]
  have hu := AnalyticSet.iUnion (s := fun b : Bool => if b then
      {x | DiskAvoidingPath (R x).crosscut.toContinuousMap (z x)
        (halfPlaneDisk ((((R x).curve ⟨0, bot_lt_top⟩).re - 1 : ℝ) : ℂ))}
      else {x | z x ∈ range (R x).crosscut})
    (fun b => by cases b; exact hhit.analyticSet; exact hleft)
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro (h | h)
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  · intro h
    obtain ⟨b, hb⟩ := mem_iUnion.mp h
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexLocal
attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local constancy of the greatest-translate index follows from the common
finite strip bound and local constancy of each of the finitely many relevant sides. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem isLocallyConstant_rayIndexSide (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) :
    IsLocallyConstant (rayIndexSide hsch γ hγ k) := by
  have hc : Continuous (fun z : RayIndexDomain γ hγ => halfPlaneDisk z.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun z => z.property.1)
  exact ((translatedHalfPlaneRay γ hγ k).isLocallyConstant_side
    (rayJordan_spec hsch γ hγ k)).comp_continuous (hc.subtype_mk _)

theorem rayIndexSide_eq_true_iff (hsch : PlanarSchoenflies) (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (z : RayIndexDomain γ hγ) :
    rayIndexSide hsch γ hγ k z = true ↔ k ∈ rayRightIndices hsch γ hγ z.val := by
  unfold rayIndexSide HalfPlaneRay.side rayRightIndices
  split_ifs <;> simp_all

theorem isLocallyConstant_geometricRayIndex (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) :
    IsLocallyConstant (fun z : RayIndexDomain γ hγ => geometricRayIndex hsch γ hγ z.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith [z.property.1]
  obtain ⟨N, _, hN⟩ := translated_sides_eventually_fixed {γ} isCompact_singleton
    (by simpa only [singleton_subset_iff] using hγ) X Y hX hY
  obtain ⟨B, hB⟩ := exists_int_gt N
  have hfar (w : RayIndexDomain γ hγ) (hwX : |w.val.re| ≤ X) (hwY : w.val.im ≤ Y) (k : ℤ) :
      (N < (k : ℝ) → k ∉ rayRightIndices hsch γ hγ w.val) ∧
      ((k : ℝ) < -N → k ∈ rayRightIndices hsch γ hγ w.val) := by
    have h := hN ⟨γ, mem_singleton γ⟩ w.val.re w.val.im hwX w.property.1 hwY k
      (rayJordan hsch γ hγ k) (rayJordan_spec hsch γ hγ k)
    have he := Complex.re_add_im w.val
    constructor
    · intro hk hm
      exact hm (he ▸ h.1 hk)
    · intro hk
      exact he ▸ h.2 hk
  have hzX : |z.val.re| ≤ X := by dsimp [X]; linarith
  have hzY : z.val.im ≤ Y := by dsimp [Y] <;> linarith
  have hnearX : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, |w.val.re| ≤ X := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => |w.val.re|) :=
      (Complex.continuous_re.comp continuous_subtype_val).abs
    have hzlt : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hnearY : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z, w.val.im ≤ Y := by
    have hc : Continuous (fun w : RayIndexDomain γ hγ => w.val.im) :=
      Complex.continuous_im.comp continuous_subtype_val
    have hzlt : z.val.im < Y := by dsimp [Y] <;> linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzlt)).mono
      (fun _ h => h.le)
  have hfinite : ∀ᶠ w : RayIndexDomain γ hγ in 𝓝 z,
      ∀ k : {k : ℤ // k ∈ Icc (-B) B}, rayIndexSide hsch γ hγ k.val w = rayIndexSide hsch γ hγ k.val z := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isLocallyConstant_rayIndexSide hsch γ hγ k.val).eventually_eq z
  filter_upwards [hnearX, hnearY, hfinite] with w hwX hwY hw
  have heq : rayRightIndices hsch γ hγ w.val = rayRightIndices hsch γ hγ z.val := by
    ext k
    by_cases hk : k ∈ Icc (-B) B
    · rw [← rayIndexSide_eq_true_iff, ← rayIndexSide_eq_true_iff, hw ⟨k, hk⟩]
    · have hsplit : k < -B ∨ B < k := by
        simpa only [mem_Icc, not_and_or, not_le] using hk
      rcases hsplit with hleft | hright
      · have hkn : (k : ℝ) < -N := by
          have hk' : (k : ℝ) < (-B : ℤ) := by exact_mod_cast hleft
          rw [Int.cast_neg] at hk'
          linarith
        exact iff_of_true ((hfar w hwX hwY k).2 hkn) ((hfar z hzX hzY k).2 hkn)
      · have hkn : N < (k : ℝ) := hB.trans (by exact_mod_cast hright)
        exact iff_of_false ((hfar w hwX hwY k).1 hkn) ((hfar z hzX hzY k).1 hkn)
  exact congrArg sSup heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GeometricIndexMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual greatest-translate index is Borel in a compact arc sample.
Its definition may use arbitrary Jordan charts; measurability does not. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem measurableSet_rayRightIndices (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) (k : ℤ) :
    MeasurableSet {γ : K | k ∈ rayRightIndices hsch γ.val (hKS γ.property) z} := by
  let : PolishSpace K := hK.isClosed.polishSpace
  apply measurableSet_rayRightFamily hsep
    (fun γ : K => translatedHalfPlaneRay γ.val (hKS γ.property) k)
    (fun γ : K => rayJordan hsch γ.val (hKS γ.property) k)
    (fun γ => rayJordan_spec hsch γ.val (hKS γ.property) k)
    (measurable_translatedCrosscut_family K hKS k)
    (Complex.continuous_re.measurable.comp (measurable_translatedRay_family K hKS k ⟨0, bot_lt_top⟩))
    (fun _ => halfPlaneDisk z) measurable_const
  intro γ
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz)

 theorem measurable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (z : ℂ) (hz : 0 ≤ z.im) :
    Measurable (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) := by
  apply measurable_of_Ioi
  intro k
  have hm := measurableSet_rayRightIndices hsch hsep K hK hKS z hz (k + 1)
  have he : {γ : K | k + 1 ∈ rayRightIndices hsch γ.val (hKS γ.property) z} =
      (fun γ : K => geometricRayIndex hsch γ.val (hKS γ.property) z) ⁻¹' Ioi k := by
    ext γ
    rw [mem_ofPred_eq, mem_rayRightIndices_iff_le hsch hsep γ.val (hKS γ.property) z hz]
    change k + 1 ≤ geometricRayIndex hsch γ.val (hKS γ.property) z ↔
      k < geometricRayIndex hsch γ.val (hKS γ.property) z
    omega
  exact he ▸ hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanGeometricIndex
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the actual geometric index of a compact arc law. Uniform
bounds come from the ray geometry, rather than a domination hypothesis. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem integrable_geometricRayIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    Integrable (fun γ : K => (geometricRayIndex hsch γ.val (hKS γ.property) z.val : ℝ))
      (η : Measure K) := by
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS |z.val.re| z.val.im
    (abs_nonneg _) z.property
  apply Integrable.of_bound
    ((show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).measurable.comp
      (measurable_geometricRayIndex hsch hsep K hK hKS z.val z.property)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro γ
  have he := Complex.re_add_im z.val
  simpa only [Function.comp_apply, he, Real.norm_eq_abs] using hM γ z.val.re z.val.im le_rfl z.property le_rfl

 theorem rayIndexDomain_of_projection_avoids (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ∀ k : ℤ, halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
  intro k hk
  obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hk
  apply hz
  refine ⟨t.val, ?_⟩
  rw [← diskRayProjection_translated γ hγ k t, ht]

 theorem continuousAt_geometricRayIndex_of_avoids (hsch : PlanarSchoenflies)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (z : ClosedUpperHalfPlane)
    (hz : diskRayProjection z.val ∉ range γ) :
    ContinuousAt (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) z := by
  let U := {w : ClosedUpperHalfPlane | diskRayProjection w.val ∉ range γ}
  have ho : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl.preimage
    (continuous_diskRayProjection.comp continuous_subtype_val)
  have hc : ContinuousOn (fun w : ClosedUpperHalfPlane =>
      (geometricRayIndex hsch γ hγ w.val : ℝ)) U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : U → RayIndexDomain γ hγ := fun w => ⟨w.val.val, w.val.property,
      rayIndexDomain_of_projection_avoids γ hγ w.val w.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (show Continuous (fun n : ℤ => (n : ℝ)) from continuous_of_discreteTopology).comp
      ((isLocallyConstant_geometricRayIndex hsch γ hγ).continuous.comp hf)
  exact hc.continuousAt (ho.mem_nhds hz)

 theorem continuousAt_meanGeometricIndex (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane)
    (hz : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection z.val ∉ range γ.val) :
    ContinuousAt (meanGeometricIndex hsch K hKS η) z := by
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith [z.property]
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hx : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, |w.val.re| ≤ X := by
    have hc := (Complex.continuous_re.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))).abs
    have hl : |z.val.re| < X := by dsimp [X]; linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  have hy : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z, w.val.im ≤ Y := by
    have hc := Complex.continuous_im.comp (continuous_subtype_val (p := fun z : ℂ => 0 ≤ z.im))
    have hl : z.val.im < Y := by dsimp [Y] <;> linarith
    exact (hc.continuousAt.eventually (isOpen_Iio.mem_nhds hl)).mono (fun _ h => h.le)
  refine tendsto_integral_filter_of_dominated_convergence (fun _ : K => M)
    (Eventually.of_forall fun w =>
      (integrable_geometricRayIndex hsch hsep K hK hKS η w).aestronglyMeasurable)
    ?_ (integrable_const M) ?_
  · filter_upwards [hx, hy] with w hwX hwY
    apply Eventually.of_forall
    intro γ
    have he := Complex.re_add_im w.val
    simpa only [he, Real.norm_eq_abs] using hM γ w.val.re w.val.im hwX w.property hwY
  · filter_upwards [hz] with γ hγ
    exact continuousAt_geometricRayIndex_of_avoids hsch γ.val (hKS γ.property) z hγ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanContinuity
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous local representatives of the geometric mean index.
Point avoidance is transported through the actual injective Jordan map. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem liftedMeanGeometricIndex_eq (hsch : PlanarSchoenflies)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (Ψ : ℂ → ℂ) (z : ℂ) (hz : 0 ≤ (Ψ z).im) :
    liftedMeanGeometricIndex hsch K hKS η Ψ z =
      meanGeometricIndex hsch K hKS η ⟨Ψ z, hz⟩ := dite_eq_left hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanIndexIntersections
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The expected distinct intersection count controls increments of the
actual averaged index. Infinite counts are allowed. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_difference_le_intersections (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K)
    (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hinj : Injective (diskRayProjection ∘ δ)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS η ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS η ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : K, pathImageCount (diskRayProjection '' range δ) γ.val ∂(η : Measure K) := by
  have h0 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 0, hδ 0⟩
  have h1 := integrable_geometricRayIndex hsch hsep K hK hKS η ⟨δ 1, hδ 1⟩
  unfold meanGeometricIndex
  rw [← integral_sub h1 h0]
  calc
    _ ≤ ∫⁻ γ : K, ‖(geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
        (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ)‖ₑ ∂(η : Measure K) := by
      simpa only [Real.enorm_eq_ofReal_abs] using enorm_integral_le_lintegral_enorm
        (μ := (η : Measure K)) (fun γ : K =>
          (geometricRayIndex hsch γ.val (hKS γ.property) (δ 1) : ℝ) -
            (geometricRayIndex hsch γ.val (hKS γ.property) (δ 0) : ℝ))
    _ ≤ _ := lintegral_mono (fun γ => by
      simpa only [Real.enorm_eq_ofReal_abs] using
        geometric_index_difference_le_intersections hsch hsep γ.val (hKS γ.property) δ hδ hinj)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCountMap
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective coordinate changes preserve the distinct intersection
bound used by the physical slice estimate. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

 theorem pathImageCount_map_le (F : C(X, Y)) (γ : C(PathTime, X)) (H : Set X)
    (hF : InjOn F (range γ ∪ H)) :
    pathImageCount (F '' H) (F.comp γ) ≤ pathImageCount H γ := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hH⟩ := hn
    have hti : Injective (γ ∘ t) := by
      intro i j hij
      exact ht (congrArg F hij)
    have hm (i : Fin n) : γ (t i) ∈ H := by
      obtain ⟨x, hx, heq⟩ := hH i
      have he : x = γ (t i) := hF (Or.inr hx) (Or.inl (mem_range_self _)) heq
      exact he ▸ hx
    rw [pathImageCount_eq_iSup]
    exact (ite_eq_left (show γ ∈ imageHitAtLeast H n from ⟨t, hti, hm⟩)).symm.le.trans
      (le_iSup (fun k => if γ ∈ imageHitAtLeast H k then (k : ℝ≥0∞) else 0) n)
  · exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_TransportedMeanIndex
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean-index increment estimate in the original physical
coordinates. The Jordan map is used only through continuity and injectivity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
 theorem meanGeometricIndex_mapped_difference_le_intersections
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (α : C(PathTime, X)) (δ : C(PathTime, ℂ)) (hδ : ∀ t, 0 ≤ (δ t).im)
    (hproj : ∀ t, diskRayProjection (δ t) = F (α t))
    (hinj : Injective (diskRayProjection ∘ δ))
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ range α)) :
    ENNReal.ofReal |meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨δ 1, hδ 1⟩ -
      meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨δ 0, hδ 0⟩| ≤
      ∫⁻ γ : A, pathImageCount (range α) γ.val ∂(η : Measure A) := by
  have hclosed : IsClosed (diskRayProjection '' range δ) :=
    ((isCompact_range δ.continuous).image continuous_diskRayProjection).isClosed
  have he : diskRayProjection '' range δ = F '' range α := by
    rw [← range_comp, ← range_comp]
    congr 1
    funext t
    exact hproj t
  apply (meanGeometricIndex_difference_le_intersections hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    δ hδ hinj).trans
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map]
  · apply lintegral_mono
    intro γ
    change pathImageCount (diskRayProjection '' range δ) (f γ).val ≤
      pathImageCount (range α) γ.val
    rw [hmap γ, he]
    exact pathImageCount_map_le F γ.val (range α) (hF γ)
  · exact (measurable_pathImageCount hclosed).comp measurable_subtype_coe
  · exact hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanIndexArcPayment
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual local branch of the averaged ray index is paid for by
the finite expected intersection measure of a prior level union. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lifted_mean_index_arc_payment
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H V : Set X} (hH : IsClosed H)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (Ψ : X → ℂ) (hΨ : ContinuousOn Ψ V)
    (hpos : ∀ x ∈ V, 0 ≤ (Ψ x).im)
    (hproj : ∀ x ∈ V, diskRayProjection (Ψ x) = F x)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ V)) (hinj : InjOn F V)
    (α : C(PathTime, X)) (hα : Injective α)
    (hαV : range α ⊆ V) (hαH : range α ⊆ H) :
    ENNReal.ofReal
      |liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ (α 1)) -
        liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ (α 0))| ≤
      meanPathIntersectionMeasure H
        ((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _) (range α) := by
  let δ : C(PathTime, ℂ) :=
    ⟨Ψ ∘ α, hΨ.comp_continuous α.continuous (fun t => hαV (mem_range_self t))⟩
  have hδ : ∀ t, 0 ≤ (δ t).im := fun t => hpos (α t) (hαV (mem_range_self t))
  have hδproj : ∀ t, diskRayProjection (δ t) = F (α t) :=
    fun t => hproj (α t) (hαV (mem_range_self t))
  have hδinj : Injective (diskRayProjection ∘ δ) := by
    intro t u h
    apply hα
    apply hinj (hαV (mem_range_self t)) (hαV (mem_range_self u))
    exact (hδproj t).symm.trans (h.trans (hδproj u))
  have hp := meanGeometricIndex_mapped_difference_le_intersections hsch hsep A K hK
    hKS η F f hf hmap α δ hδ hδproj hδinj
    (fun γ => (hF γ).mono (union_subset_union_right _ hαV))
  have hν : meanPathIntersectionMeasure H
      ((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _) (range α) =
      ∫⁻ γ : A, pathImageCount (range α) γ.val ∂(η : Measure A) := by
    rw [meanPathIntersectionMeasure_apply_subset H hH _ hfinite (range α)
      (isCompact_range α.continuous).isClosed.measurableSet hαH,
      ProbabilityMeasure.toMeasure_map]
    exact lintegral_map (measurable_pathImageCount
      (isCompact_range α.continuous).isClosed) measurable_subtype_coe
  rw [hν, liftedMeanGeometricIndex_eq hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ (α 1)) (hδ 1),
    liftedMeanGeometricIndex_eq hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ (α 0)) (hδ 0)]
  exact hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_1
theorem lintegral_sphericalArea (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻x, g x ∂sphericalArea =
      ∫⁻z : ℂ, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  rw [sphericalArea, lintegral_map hg OnePoint.continuous_coe.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (hg.comp OnePoint.continuous_coe.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CircleNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null images of local circle-valued traces

Projection modulo one preserves real outer-null sets. A countable family
of null real branches therefore gives a null image in the circle with
its Haar measure of total mass one.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem volume_addCircle_image_eq_zero {A : Set ℝ} (hA : volume A = 0) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' A) = 0 := by
  have hpiece (a : ℝ) :
      volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1))) = 0 := by
    let e := AddCircle.measurableEquivIoc (1 : ℝ) a
    let S : Set (Ioc a (a + 1)) := Subtype.val ⁻¹' A
    have he : MeasurePreserving e volume (volume.comap Subtype.val) :=
      AddCircle.measurePreserving_equivIoc (1 : ℝ)
    have hset : e ⁻¹' S = ((↑) : ℝ → AddCircle (1 : ℝ)) '' (A ∩ Ioc a (a + 1)) := by
      ext y
      constructor
      · intro hy
        refine ⟨(e y).val, ⟨hy, (e y).property⟩, ?_⟩
        exact AddCircle.coe_equivIoc
      · rintro ⟨x, hx, rfl⟩
        change (AddCircle.equivIoc (1 : ℝ) a (x : AddCircle (1 : ℝ))).val ∈ A
        rw [AddCircle.equivIoc_coe_eq hx.2]
        exact hx.1
    rw [← hset, he.measure_preimage_equiv S,
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).comap_apply]
    apply measure_mono_null _ hA
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcover : ((↑) : ℝ → AddCircle (1 : ℝ)) '' A ⊆
      ⋃ k : ℤ, ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        (A ∩ Ioc ((k : ℝ) - 1) ((k : ℝ) - 1 + 1)) := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⌈x⌉, x, ⟨hx, ?_⟩, rfl⟩
    have hlo := Int.ceil_lt_add_one x
    have hhi := Int.le_ceil x
    constructor <;> linarith
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun k => hpiece ((k : ℝ) - 1))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ComponentTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null traces on the nondegenerate components of a level union

Generic level unions have only countably many nondegenerate components.
Consequently a trace that is null on each such component is null on their
union. At free points the new coordinate has one trace value, so the
levels meeting this union form a Haar-null set. This is the fixed-prior-
tuple step in the manuscript's compatibility argument.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem volume_trace_nontrivialComponentLocus_eq_zero
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (F : Set X)
    (w : X → AddCircle (1 : ℝ))
    (hnull : ∀ C : Set X, (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume (w '' (F ∩ C)) = 0) :
    volume (w '' (F ∩ nontrivialComponentLocus X)) = 0 := by
  let S : Set (Set X) := {C | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}
  have hS : S.Countable := countable_nontrivial_connectedComponents hbound
  have hcover : w '' (F ∩ nontrivialComponentLocus X) ⊆
      ⋃ C ∈ S, w '' (F ∩ C) := by
    rintro t ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨connectedComponent x,
      mem_iUnion.mpr ⟨⟨⟨x, rfl⟩, hx.2⟩, x, ⟨hx.1, mem_connectedComponent⟩, rfl⟩⟩
  apply measure_mono_null hcover
  exact (measure_biUnion_null_iff hS).mpr (fun C hC => hnull C hC.1 hC.2)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LusinInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Completed-measure compatibility for finite level tuples

Lusin's universal-measurability theorem applies to the finite-dimensional
tori used for level choices:
A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
Theorem 21.10, p. 155. Every analytic subset of a standard Borel space is
measurable for the completion of each sigma-finite Borel measure.
Publisher: https://doi.org/10.1007/978-1-4612-4190-4

The compatibility statement uses analyticity of compact incidence sets
and nullity of the free trace image on each nondegenerate component.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

/-- The ambient version of the nondegenerate-component locus agrees
with the image of the corresponding locus in the level subtype. -/
theorem nontrivialComponentInLocus_eq_image
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    {x | (connectedComponentIn A x).Nontrivial} =
      Subtype.val '' nontrivialComponentLocus A := by
  ext x
  constructor
  · intro hx
    change (connectedComponentIn A x).Nontrivial at hx
    have hxA : x ∈ A := by
      by_contra hn
      exact Set.not_nontrivial_empty (connectedComponentIn_eq_empty hn ▸ hx)
    rw [connectedComponentIn_eq_image hxA] at hx
    exact ⟨⟨x, hxA⟩, nontrivial_of_image _ _ hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change (connectedComponentIn A x.val).Nontrivial
    rw [connectedComponentIn_eq_image x.property]
    exact hx.image Subtype.val_injective

/-- Null component traces give a null trace image on the ambient
nondegenerate-component locus of a compact level union. -/
theorem volume_trace_nontrivialComponentInLocus_eq_zero
    {X : Type*} [MetricSpace X] (A : Set X) [CompactSpace A]
    (hbound : HasFiniteLargeContinuumBound A) (F : Set X)
    (w : X → UnitAddCircle)
    (hnull : ∀ C : Set A, (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume ((fun x : A => w x) '' ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    volume (w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial})) = 0 := by
  have hn := volume_trace_nontrivialComponentLocus_eq_zero hbound
    (Subtype.val ⁻¹' F) (fun x : A => w x) hnull
  have heq : w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial}) =
      (fun x : A => w x) '' ((Subtype.val ⁻¹' F) ∩ nontrivialComponentLocus A) := by
    rw [nontrivialComponentInLocus_eq_image]
    ext t
    constructor
    · rintro ⟨x, ⟨hxF, y, hy, rfl⟩, ht⟩
      exact ⟨y, ⟨hxF, hy⟩, ht⟩
    · rintro ⟨x, ⟨hxF, hxC⟩, ht⟩
      exact ⟨x, ⟨hxF, x, hxC, rfl⟩, ht⟩
  rwa [heq]

/-- Fubini's null-section implication with the other order of factors.
The event need only be measurable in the completed product measure. -/
theorem product_null_of_nullMeasurable_swapped_sections
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {E : Set (A × B)} (hE : NullMeasurableSet E (μ.prod ν))
    (hsections : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' E) = 0) :
    (μ.prod ν) E = 0 := by
  have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have hpre : NullMeasurableSet (Prod.swap ⁻¹' E) (ν.prod μ) :=
    hE.preimage hswap.quasiMeasurePreserving
  have hzero : (ν.prod μ) (Prod.swap ⁻¹' E) = 0 :=
    product_null_of_nullMeasurable_sections hpre hsections
  rw [hswap.measure_preimage hE] at hzero
  exact hzero

/-- An analytic compatibility failure is measurable for the completed
product law, using analytic measurability on finite tori. -/
theorem nullMeasurableSet_freeComponentFailure
    {X Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hLusin : FiniteTorusAnalyticMeasurability) (d : ℕ)
    {F : Set X} (hF : MeasurableSet F)
    {Rnew : Set (X × UnitAddCircle)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × UnitAddCircle)} (hR : ∀ l, IsClosed (R l))
    (labels : Fin d → Λ) :
    NullMeasurableSet (freeComponentFailure F Rnew R labels)
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) :=
  hLusin d _ (analyticSet_freeComponentFailure hF hnew hR labels)

/-- For one fixed prior tuple, null component traces exclude all new
levels except a Haar-null set. No measurability of the trace is needed. -/
theorem measure_new_level_failure_eq_zero
    {X Λ : Type*} [MetricSpace X] [CompactSpace X]
    (F : Set X) (Rnew : Set (X × UnitAddCircle))
    (R : Λ → Set (X × UnitAddCircle)) (d : ℕ) (labels : Fin d → Λ)
    (θ : Fin d → UnitAddCircle) (w : X → UnitAddCircle)
    (hlevel : ∀ x ∈ F, ∀ t, (x, t) ∈ Rnew ↔ w x = t)
    (hA : IsClosed {x | (x, θ) ∈ finiteLevelUnionGraph R labels})
    (hbound : HasFiniteLargeContinuumBound
      {x | (x, θ) ∈ finiteLevelUnionGraph R labels})
    (hnull : ∀ C : Set {x | (x, θ) ∈ finiteLevelUnionGraph R labels},
      (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume ((fun x : {x | (x, θ) ∈ finiteLevelUnionGraph R labels} => w x) ''
        ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    volume ((fun t => (t, θ)) ⁻¹' freeComponentFailure F Rnew R labels) = 0 := by
  let A := {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have htrace := volume_trace_nontrivialComponentInLocus_eq_zero A hbound F w hnull
  apply measure_mono_null (t := w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial})) _ htrace
  intro t ht
  obtain ⟨⟨x, t', θ'⟩, hx, heq⟩ := ht
  cases heq
  exact ⟨x, ⟨hx.1, hx.2.2⟩, (hlevel x hx.1 t).mp hx.2.1⟩

/-- The finite-tuple compatibility conclusion, conditional on the
analytic measurability on finite tori and the null-trace
hypotheses. Repeated prior labels are allowed. -/
theorem measure_freeComponentFailure_eq_zero
    {X Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hLusin : FiniteTorusAnalyticMeasurability) (d : ℕ)
    {F : Set X} (hF : MeasurableSet F)
    {Rnew : Set (X × UnitAddCircle)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × UnitAddCircle)} (hR : ∀ l, IsClosed (R l))
    (labels : Fin d → Λ) (w : X → UnitAddCircle)
    (hlevel : ∀ x ∈ F, ∀ t, (x, t) ∈ Rnew ↔ w x = t)
    (hgood : ∀ᵐ θ ∂Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)),
      HasFiniteLargeContinuumBound {x | (x, θ) ∈ finiteLevelUnionGraph R labels} ∧
      ∀ C : Set {x | (x, θ) ∈ finiteLevelUnionGraph R labels},
        (∃ x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : {x | (x, θ) ∈ finiteLevelUnionGraph R labels} => w x) ''
          ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin d => volume)))
      (freeComponentFailure F Rnew R labels) = 0 := by
  apply product_null_of_nullMeasurable_swapped_sections
    (nullMeasurableSet_freeComponentFailure hLusin d hF hnew hR labels)
  filter_upwards [hgood] with θ hθ
  have hA : IsClosed {x | (x, θ) ∈ finiteLevelUnionGraph R labels} :=
    (isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)
  exact measure_new_level_failure_eq_zero F Rnew R d labels θ w hlevel hA hθ.1 hθ.2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TraceBandLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a point with a genuine limiting real trace, the entire circle
band is the single projected trace value. -/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_trace
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X] {G : Set X} {u : X → ℝ} {M : ℝ}
    (hM : ∀x ∈ G, |u x| ≤ M) {x : X} (hx : x ∈ closure G) {v : ℝ}
    (htrace : Tendsto u (𝓝[G] x) (𝓝 v)) {t : AddCircle (1 : ℝ)} :
    (x, t) ∈ circleBandGraph G u ↔ (v : AddCircle (1 : ℝ)) = t := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hband : ∀r : ℝ, (x, r) ∈ intervalFiberHull (clusterGraph G u) ↔ r = v := by
    intro r
    have he := intervalFiberHull_clusterGraph_eq_boundary_band hM hx
    have hr := Set.ext_iff.mp he r
    simpa only [mem_ofPred_eq, htrace.liminf_eq, htrace.limsup_eq, Icc_self,
      mem_singleton_iff] using hr
  constructor
  · rintro ⟨⟨y, r⟩, hr, heq⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj heq
    rwa [(hband r).mp hr] at ht
  · intro ht
    exact ⟨(x, v), (hband v).mpr rfl, Prod.ext rfl ht⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_BoundaryTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unique traces outside the countable band support

For a bounded real coordinate the interval band is the actual interval
between the lower and upper boundary limits. A zero band budget forces
these limits to agree and gives convergence from the physical domain.
Square summability of the budgets makes all exceptions countable.
-/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem countable_band_support {X : Type*} {a : X → ℝ}
    (ha : Summable (fun x => a x ^ 2)) : {x | a x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using ha.countable_support

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedHausdorffImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Hausdorff-measure estimates for the finite sphere chart.
The estimates are proved from the library's Lipschitz Hausdorff bound. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

theorem lipschitzOn_hausdorff_restrict_le_map
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) :
    (μH[1] : Measure Y).restrict (f '' S) ≤
      (K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f := by
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.map_apply hf hT,
    Measure.restrict_apply (hf hT)]
  have heq : T ∩ f '' S = f '' (f ⁻¹' T ∩ S) := by
    ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxS⟩, rfl⟩
      exact ⟨hx, x, hxS, rfl⟩
  rw [heq]
  simpa only [ENNReal.rpow_one, smul_eq_mul] using
    (hK.mono inter_subset_right).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)

theorem lipschitzOn_lintegral_hausdorff_image_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K f S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      (K : ℝ≥0∞) * ∫⁻x in S, g (f x) ∂(μH[1] : Measure X) := by
  calc
    _ ≤ ∫⁻y, g y ∂((K : ℝ≥0∞) • ((μH[1] : Measure X).restrict S).map f) :=
      lintegral_mono' (lipschitzOn_hausdorff_restrict_le_map hf hK) le_rfl
    _ = _ := by rw [lintegral_smul_measure, lintegral_map hg hf, smul_eq_mul]

theorem lintegral_hausdorff_image_le_of_partition
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) (A : ℕ → Set X)
    (hA : ∀n, MeasurableSet (A n)) (hdisj : Pairwise (Disjoint on A))
    (hcover : ⋃n, A n = univ) (K : ℕ → ℝ≥0)
    (hK : ∀n, LipschitzOnWith (K n) f (A n))
    (w : X → ℝ≥0∞)
    (hweight : ∀n x, x ∈ A n → (K n : ℝ≥0∞) ≤ w x)
    {S : Set X} (hS : MeasurableSet S) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in f '' S, g y ∂(μH[1] : Measure Y)) ≤
      ∫⁻x in S, w x * g (f x) ∂(μH[1] : Measure X) := by
  have hsets : ⋃n, S ∩ A n = S := by rw [← inter_iUnion, hcover, inter_univ]
  calc
    _ = ∫⁻y in ⋃n, f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) := by
      rw [← image_iUnion, hsets]
    _ ≤ ∑'n, ∫⁻y in f '' (S ∩ A n), g y ∂(μH[1] : Measure Y) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑'n, ∫⁻x in S ∩ A n, w x * g (f x) ∂(μH[1] : Measure X) := by
      apply ENNReal.tsum_le_tsum
      intro n
      calc
        _ ≤ (K n : ℝ≥0∞) * ∫⁻x in S ∩ A n, g (f x) ∂(μH[1] : Measure X) :=
          lipschitzOn_lintegral_hausdorff_image_le hf ((hK n).mono inter_subset_right) g hg
        _ = ∫⁻x in S ∩ A n, (K n : ℝ≥0∞) * g (f x) ∂(μH[1] : Measure X) :=
          (lintegral_const_mul _ (hg.comp hf)).symm
        _ ≤ _ := setLIntegral_mono' (hS.inter (hA n)) fun x hx =>
          mul_le_mul' (hweight n x hx.2) le_rfl
    _ = _ := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n))
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right), hsets]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GlobalSphericalDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The decaying finite-chart density is globally square integrable.
No compact restriction is needed after inserting the spherical factor. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem spherical_weight_sq_le_areaDensity (z : ℂ) :
    (1 / (1 + ‖z‖ ^ 2)) ^ 2 ≤ sphericalAreaDensity z := by
  rw [div_pow, one_pow, sphericalAreaDensity]
  exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_StereographicDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decay of the derivative of the fixed inverse stereographic map.
This supplies the spherical weight missing from a compact-chart bound. -/

open Set Function
open scoped RealInnerProductSpace

noncomputable section

namespace CircleDomainRigidity

theorem stereoInvFunAux_eq_centered (v w : RoundAmbient) :
    stereoInvFunAux v w =
      v + (4 / (‖w‖ ^ 2 + 4)) • (w - (2 : ℝ) • v) := by
  have hn : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have h1 : (‖w‖ ^ 2 + 4)⁻¹ * 4 = 4 / (‖w‖ ^ 2 + 4) := by ring
  have h2 : (‖w‖ ^ 2 + 4)⁻¹ * (‖w‖ ^ 2 - 4) =
      1 - (4 / (‖w‖ ^ 2 + 4)) * 2 := by
    field_simp
    ring
  simp only [stereoInvFunAux, smul_add, smul_smul, h1, h2]
  module

theorem stereographic_scalar_bound {r : ℝ} (hr : 0 ≤ r) :
    4 / (r ^ 2 + 4) + 8 * r * (r + 2) / (r ^ 2 + 4) ^ 2 ≤
      16 / (r ^ 2 + 4) := by
  have hD : 0 < r ^ 2 + 4 := by positivity
  have hpoly : 4 * (r ^ 2 + 4) + 8 * r * (r + 2) ≤ 16 * (r ^ 2 + 4) := by
    nlinarith [sq_nonneg (r - 2)]
  calc
    _ = (4 * (r ^ 2 + 4) + 8 * r * (r + 2)) / (r ^ 2 + 4) ^ 2 := by
      field_simp
    _ ≤ (16 * (r ^ 2 + 4)) / (r ^ 2 + 4) ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2 hpoly
    _ = _ := by field_simp

theorem stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) :
    (fderiv ℝ (stereoInvFunAux v) w) h =
      (4 / (‖w‖ ^ 2 + 4)) • h -
        (8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v) := by
  let D : ℝ := ‖w‖ ^ 2 + 4
  have hD : D ≠ 0 := by dsimp [D] <;> positivity
  have hQ := (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const (4 : ℝ)
  have ha : HasFDerivAt (fun z : RoundAmbient => 4 / (‖z‖ ^ 2 + 4))
      ((-8 / D ^ 2) • innerSL ℝ w) w := by
    convert ((hasFDerivAt_inv hD).comp w hQ).const_mul (4 : ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    · funext z
      simp only [Function.comp_apply, div_eq_mul_inv]
    · ext z
      simp only [ContinuousLinearMap.comp_apply, smul_apply, innerSL_apply_apply,
        smul_eq_mul]
      dsimp [D]
      ring
  have hF := (hasFDerivAt_const v w).add
    (ha.smul ((hasFDerivAt_id w).sub_const ((2 : ℝ) • v)))
  have heq : stereoInvFunAux v =
      fun z : RoundAmbient => v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v) :=
    funext (stereoInvFunAux_eq_centered v)
  have hd := hF.fderiv
  change fderiv ℝ (fun z : RoundAmbient =>
    v + (4 / (‖z‖ ^ 2 + 4)) • (z - (2 : ℝ) • v)) w = _ at hd
  rw [heq, hd]
  simp only [zero_add, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
  dsimp [D]
  module

theorem norm_stereoInvFunAux_fderiv_apply (v w h : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖(fderiv ℝ (stereoInvFunAux v) w) h‖ ≤
      (16 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
  have hD : 0 < ‖w‖ ^ 2 + 4 := by positivity
  have hc : |8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2| ≤
      8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2 := by
    calc
      _ = 8 * |inner ℝ w h| / (‖w‖ ^ 2 + 4) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hD)]
        norm_num
      _ ≤ 8 * (‖w‖ * ‖h‖) / (‖w‖ ^ 2 + 4) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w h) (by norm_num))
          (sq_nonneg _)
      _ = _ := by ring
  have hvect : ‖w - (2 : ℝ) • v‖ ≤ ‖w‖ + 2 := by
    calc
      _ ≤ ‖w‖ + ‖(2 : ℝ) • v‖ := norm_sub_le _ _
      _ = ‖w‖ + 2 * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]; norm_num
      _ ≤ _ := by linarith
  have hfirst : ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ = (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hD)]
  have hsecond : ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ ≤
      (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hvect (norm_nonneg _) (by positivity)
  rw [stereoInvFunAux_fderiv_apply]
  calc
    _ ≤ ‖(4 / (‖w‖ ^ 2 + 4)) • h‖ +
        ‖(8 * inner ℝ w h / (‖w‖ ^ 2 + 4) ^ 2) • (w - (2 : ℝ) • v)‖ := norm_sub_le _ _
    _ ≤ (4 / (‖w‖ ^ 2 + 4)) * ‖h‖ +
        (8 * ‖w‖ * ‖h‖ / (‖w‖ ^ 2 + 4) ^ 2) * (‖w‖ + 2) :=
      add_le_add hfirst.le hsecond
    _ = (4 / (‖w‖ ^ 2 + 4) + 8 * ‖w‖ * (‖w‖ + 2) / (‖w‖ ^ 2 + 4) ^ 2) * ‖h‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (stereographic_scalar_bound (norm_nonneg w)) (norm_nonneg h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartDerivativeDecay
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global inverse-quadratic derivative bound for the chosen finite sphere chart. -/

open Set Function

noncomputable section

namespace CircleDomainRigidity

theorem norm_stereoInvFunAux_fderiv (v w : RoundAmbient) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (stereoInvFunAux v) w‖ ≤ 16 / (‖w‖ ^ 2 + 4) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  exact norm_stereoInvFunAux_fderiv_apply v w h hv

theorem norm_linearSphereChartMap (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) :
    ‖linearSphereChartMap v A‖ ≤ ‖A.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (linearSphereChartMap v A)
    (norm_nonneg A.toContinuousLinearMap)
  intro h
  exact A.toContinuousLinearMap.le_opNorm h

theorem linear_stereo_fderiv (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z =
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)).comp (linearSphereChartMap v A) := by
  have hA : HasFDerivAt (fun z : ℂ => (A z : RoundAmbient)) (linearSphereChartMap v A) z :=
    (ℝ ∙ v)ᗮ.subtypeL.hasFDerivAt.comp z A.hasFDerivAt
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux v) := contDiff_stereoInvFunAux
  have hD : DifferentiableAt ℝ (stereoInvFunAux v) (A z : RoundAmbient) :=
    (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  have hFD : HasFDerivAt (stereoInvFunAux v)
      (fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)) (A z : RoundAmbient) :=
    hD.hasFDerivAt
  have heq := (hFD.comp z hA).fderiv
  exact heq

theorem linear_stereo_derivative_decay
    (v : RoundAmbient) (hv : ‖v‖ ≤ 1) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
      (16 * ‖A.toContinuousLinearMap‖ * (1 + ‖A.symm.toContinuousLinearMap‖ ^ 2)) /
        (1 + ‖z‖ ^ 2) := by
  rw [linear_stereo_fderiv]
  calc
    _ ≤ ‖fderiv ℝ (stereoInvFunAux v) (A z : RoundAmbient)‖ *
        ‖linearSphereChartMap v A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (16 / (‖A z‖ ^ 2 + 4)) * ‖A.toContinuousLinearMap‖ :=
      mul_le_mul (norm_stereoInvFunAux_fderiv v _ hv) (norm_linearSphereChartMap v A)
        (norm_nonneg _) (by positivity)
    _ = 16 * ‖A.toContinuousLinearMap‖ / (‖A z‖ ^ 2 + 4) := by ring
    _ ≤ _ := linear_chart_inverse_quadratic_bound A z

theorem finite_sphere_chart_derivative_decay :
    ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2) := by
  classical
  have hlin (v : RoundAmbient) (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (hv : ‖v‖ ≤ 1) :
      ∃C : ℝ, 0 ≤ C ∧ ∀z : ℂ,
        ‖fderiv ℝ (fun z : ℂ => stereoInvFunAux v (A z : RoundAmbient)) z‖ ≤
          C / (1 + ‖z‖ ^ 2) :=
    ⟨_, by positivity, linear_stereo_derivative_decay v hv A⟩
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply hlin
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartSmallSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative finite-chart Lipschitz constants on small convex sets. -/

open Set Metric
open scoped NNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem quadratic_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) :
    1 + ‖x‖ ^ 2 ≤ 3 * (1 + ‖y‖ ^ 2) := by
  have hnorm : ‖x‖ ≤ ‖y‖ + 1 := by
    have hn := norm_sub_norm_le x y
    rw [← dist_eq_norm] at hn
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  nlinarith [sq_nonneg (‖y‖ - 1)]

theorem decay_weight_compare {x y : ℂ} (hxy : dist x y ≤ 1) {C : ℝ} (hC : 0 ≤ C) :
    C / (1 + ‖y‖ ^ 2) ≤ 3 * C / (1 + ‖x‖ ^ 2) := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hy : 0 < 1 + ‖y‖ ^ 2 := by positivity
  apply (div_le_div_iff₀ hy hx).2
  nlinarith [mul_le_mul_of_nonneg_left (quadratic_weight_compare hxy) hC]

theorem finite_sphere_chart_lipschitz_on_small_convex
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {K : Set ℂ} (hK : Convex ℝ K) (hne : K.Nonempty)
    (hdiam : ∀x ∈ K, ∀y ∈ K, dist x y ≤ 1) :
    ∃L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K ∧
      ∀z ∈ K, (L : ℝ) ≤ 9 * C / (1 + ‖z‖ ^ 2) := by
  obtain ⟨c, hc⟩ := hne
  let L : ℝ≥0 := ⟨3 * C / (1 + ‖c‖ ^ 2), by positivity⟩
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hLip : LipschitzOnWith L F K :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt)
      (fun z hz => by
        change ‖fderiv ℝ F z‖₊ ≤ L
        exact_mod_cast (hderiv z).trans (decay_weight_compare (hdiam c hc z hz) hC)) hK
  refine ⟨L, ?_, ?_⟩
  · intro z hz w hw
    exact hLip hz hw
  · intro z hz
    change 3 * C / (1 + ‖c‖ ^ 2) ≤ _
    have h := decay_weight_compare (hdiam z hz c hc) (show 0 ≤ 3 * C by positivity)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalWeightedLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical metric contributes its decay factor to weighted level
length. No pointwise finiteness of the nonnegative density is required. -/

open Set Function Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_rbedb44_1 : BorelSpace Sphere := ⟨rfl⟩
theorem finite_sphere_chart_weighted_length_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {S : Set ℂ} (hS : MeasurableSet S) (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in ((↑) : ℂ → Sphere) '' S, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in S, ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq ℂ
  let V : ℕ → Set ℂ := fun n => closedBall (c n) (1 / 2)
  have hV (n : ℕ) : MeasurableSet (V n) := isClosed_closedBall.measurableSet
  have hcover : ⋃n, V n = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := hc.exists_dist_lt z (by norm_num : (0 : ℝ) < 1 / 2)
    exact mem_iUnion.mpr ⟨n, hn.le⟩
  have hsmall (n : ℕ) : ∀x ∈ V n, ∀y ∈ V n, dist x y ≤ 1 := by
    intro x hx y hy
    have h1 : dist x (c n) ≤ 1 / 2 := hx
    have h2 : dist (c n) y ≤ 1 / 2 := by
      change dist y (c n) ≤ 1 / 2 at hy
      simpa only [dist_comm] using hy
    exact (dist_triangle x (c n) y).trans (by linarith)
  choose K hK hweight using fun n => finite_sphere_chart_lipschitz_on_small_convex
    hC hderiv (convex_closedBall (c n) (1 / 2))
      (nonempty_closedBall.mpr (by norm_num)) (hsmall n)
  apply lintegral_hausdorff_image_le_of_partition OnePoint.continuous_coe.measurable
    (disjointed V) (MeasurableSet.disjointed hV) (disjoint_disjointed V)
    (by rw [iUnion_disjointed, hcover]) K
    (fun n => (hK n).mono (disjointed_subset V n))
    (fun z => ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)))
    (fun n z hz => ?_) hS g hg
  have hw := ENNReal.ofReal_le_ofReal (hweight n z (disjointed_subset V n hz))
  simpa using hw

theorem spherical_weighted_density_sq_finite
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  rw [lintegral_sphericalArea _ (hg.pow_const 2)] at he
  apply lt_of_le_of_lt (lintegral_mono fun z => ?_) he
  rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl

theorem spherical_weighted_length_le_chart
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A : Set Sphere) (hA : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y in A, g y ∂(μH[1] : Measure Sphere)) ≤
      ∫⁻z in ((↑) : ℂ → Sphere) ⁻¹' A,
        ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
          ∂(μH[1] : Measure ℂ) := by
  let : NullSingletonClass (μH[1] : Measure Sphere) :=
    Measure.nullSingletonClass_hausdorff Sphere (by norm_num)
  have hcover : A ⊆ ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
      {OnePoint.infty} := by
    intro y hy
    cases y using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z => exact Or.inl ⟨z, hy, rfl⟩
  calc
    _ ≤ ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A) ∪
        {OnePoint.infty}, g y ∂(μH[1] : Measure Sphere) := lintegral_mono_set hcover
    _ ≤ (∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere)) +
        ∫⁻y in ({OnePoint.infty} : Set Sphere), g y ∂(μH[1] : Measure Sphere) :=
      lintegral_union_le _ _ _
    _ = ∫⁻y in ((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' A),
        g y ∂(μH[1] : Measure Sphere) := by simp
    _ ≤ _ := finite_sphere_chart_weighted_length_le hC hderiv hA g hg

theorem scaled_spherical_weighted_density_sq_finite
    (C : ℝ) (hC : 0 ≤ C) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z : ℂ, (ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)) ^ 2) < ∞ := by
  have heq (z : ℂ) : ENNReal.ofReal (C / (1 + ‖z‖ ^ 2)) =
      ENNReal.ofReal C * ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) := by
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  simp_rw [heq, mul_assoc, mul_pow]
  rw [lintegral_const_mul' _ _ (by finiteness)]
  apply ENNReal.mul_lt_top (by finiteness)
  simpa only [mul_pow] using spherical_weighted_density_sq_finite g hg he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CircleAlmostEverywhere
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-everywhere assertions on the unit circle from their real
representatives. No measurability of the asserted property is required. -/

open Set MeasureTheory

namespace CircleDomainRigidity

theorem ae_circle_of_ae_unit_interval (P : UnitAddCircle → Prop)
    (hP : ∀ᵐ(r : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1), P (r : UnitAddCircle)) :
    ∀ᵐ(t : UnitAddCircle) ∂volume, P t := by
  rw [restrict_Ico_eq_restrict_Ioc] at hP
  have hnull : volume ({r : ℝ | ¬P (r : UnitAddCircle)} ∩ Ioc 0 1) = 0 := by
    simpa only [ae_iff, Measure.restrict_apply' measurableSet_Ioc] using hP
  have hcircle := volume_addCircle_image_eq_zero hnull
  rw [ae_iff]
  apply measure_mono_null _ hcircle
  intro t ht
  let r := AddCircle.equivIoc (1 : ℝ) 0 t
  have hr : (r.val : UnitAddCircle) = t := AddCircle.coe_equivIoc
  refine ⟨r.val, ⟨?_, by simpa using r.property⟩, hr⟩
  change ¬P (r.val : UnitAddCircle)
  change ¬P t at ht
  rwa [hr]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical weighted length of almost every circle-valued level,
from exactly the published scalar planar coarea input. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_rbedb44_2 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_finite_spherical_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞)
    (A : UnitAddCircle → Set Sphere)
    (hA : ∀t : UnitAddCircle, ((↑) : ℂ → Sphere) ⁻¹' A t =
      D ∩ {z | (f z : UnitAddCircle) = t})
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume, (∫⁻y in A t, g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let q : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (9 * C / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hq : Measurable q := by
    apply Measurable.mul
    · apply Measurable.ennreal_ofReal
      apply Continuous.measurable
      exact continuous_const.div (continuous_const.add (continuous_norm.pow 2))
        (fun z => ne_of_gt (by positivity))
    · exact hg.comp OnePoint.continuous_coe.measurable
  have hq2 : (∫⁻z in D, q z ^ 2) < ∞ :=
    (lintegral_mono_set (subset_univ D)).trans_lt (by
      simpa only [Measure.restrict_univ] using
        scaled_spherical_weighted_density_sq_finite (9 * C) (by positivity) g hg henergy)
  have hfinite := (weighted_circle_coarea_extended_finite_energy hcoarea hD hf q hq hq2 hf2).2.2
  apply ae_circle_of_ae_unit_interval
  filter_upwards [hfinite] with t ht
  have hS : MeasurableSet (((↑) : ℂ → Sphere) ⁻¹' A (t : UnitAddCircle)) := by
    rw [hA, unitAddCircle_level_inter_eq_iUnion_integer_levels]
    exact MeasurableSet.iUnion fun k => measurableSet_scalar_level hD hf.continuousOn _
  apply lt_of_le_of_lt (spherical_weighted_length_le_chart hC hderiv _ hS g hg)
  simpa only [hA, weightedCircleLevelLength, q] using ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBarrierTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual real tests used by the countable selection. Compatibility is
with every finite sublist of previously selected tests, retaining repetitions. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace UngatedRealTest
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {EStar : Set Sphere}

omit [MeasurableSpace C(PathTime, Sphere)] in
theorem freeComponentFailure_congr_selected
    {X T I J K : Type*} [TopologicalSpace X]
    (F : Set X) (N : Set (X × T)) (R : I → Set (X × T)) (S : J → Set (X × T))
    (a : K → I) (b : K → J) (h : ∀ k, R (a k) = S (b k)) :
    freeComponentFailure F N R a = freeComponentFailure F N S b := by
  have he : finiteLevelUnionGraph R a = finiteLevelUnionGraph S b := by
    unfold finiteLevelUnionGraph
    apply iUnion_congr
    intro k
    rw [h k]
  unfold freeComponentFailure
  rw [he]

end UngatedRealTest
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted collars in the physical plane and their actual open quotient
neighborhoods. Compact containment survives projection. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem point_mem_region (hsurj : Surjective π) (hp : p ≠ π OnePoint.infty) :
    p ∈ D.region := by
  obtain ⟨x, hx⟩ := hsurj p
  cases x using OnePoint.rec with
  | infty => exact (hp hx.symm).elim
  | coe z => exact ⟨z, ⟨z, D.fiber_inside hx, rfl⟩, hx⟩

end WeightedCollar

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcIntersectionCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Distinct intersections decrease under subarc selection. Conditioning
on a compact family of mass at least one half costs at most a factor two. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_mono_range (H : Set X) {α γ : C(PathTime, X)}
    (h : range α ⊆ range γ) : pathImageCount H α ≤ pathImageCount H γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range α ∩ H
  · have hy : x ∈ range γ ∩ H := ⟨h hx.1, hx.2⟩
    simp only [hx, hy, ite_true, if_true, le_refl]
  · simp only [hx, ite_false, if_false, zero_le]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_subarc_intersections_le
    (μ η : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)))
    {H : Set X} (hH : IsClosed H) :
    (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, X))) ≤
      2 * ∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, X)) := by
  calc
    _ ≤ ∫⁻ α, pathImageCount H α ∂((2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X))) :=
      lintegral_mono' hη le_rfl
    _ = 2 * ∫⁻ γ, pathImageCount H (f γ) ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_smul_measure, ProbabilityMeasure.toMeasure_map,
        lintegral_map' (measurable_pathImageCount hH).aemeasurable hf]
      rfl
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_ae (hs.mono fun _ h => pathImageCount_mono_range H h))

theorem finite_mean_subarc_intersections
    (μ η : ProbabilityMeasure C(PathTime, X)) (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤ (2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)))
    {H : Set X} (hH : IsClosed H)
    (hfin : (∫⁻ γ, pathImageCount H γ ∂(μ : Measure C(PathTime, X))) < ∞) :
    (∫⁻ α, pathImageCount H α ∂(η : Measure C(PathTime, X))) < ∞ :=
  (mean_subarc_intersections_le μ η f hf hs hη hH).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hfin)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CenteredTerminalLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete centered disk data of a compact terminal-arc family. All
injectivity and unit bounds hold on the actual punctured Jordan interior. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

namespace CenteredTerminalFamily
variable {J : ℂ ≃ₜ ℂ} {b : Sphere} {A : Set C(PathTime, Sphere)}
    (P : CenteredTerminalFamily J b A)
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)

 theorem punctured_open : IsOpen P.punctured :=
  (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)).sdiff isClosed_singleton

 include hb

 theorem nonzero : ∀ x ∈ P.punctured, P.map x ≠ 0 := by
  intro x hx he
  apply hx.2
  apply (centeredJordanCoordinate_injOn J hb (subset_closure hx.1) (subset_closure hb))
  rw [← P.map_eq (subset_closure hx.1), centeredJordanCoordinate_self]
  exact he

 theorem norm_lt : ∀ x ∈ ((↑) : ℂ → Sphere) '' jordanInterior J, ‖P.map x‖ < 1 := by
  intro x hx
  rw [P.map_eq (subset_closure hx)]
  exact diskCentering_norm_lt (sphereJordanCoordinate_norm_lt J hb)
    (sphereJordanCoordinate_norm_lt J hx)

 theorem norm_le : ∀ x ∈ P.punctured, ‖P.map x‖ ≤ 1 :=
  fun x hx => (P.norm_lt hb x hx.1).le

 theorem injective : InjOn P.map (closure (((↑) : ℂ → Sphere) '' jordanInterior J)) := by
  intro x hx y hy he
  apply centeredJordanCoordinate_injOn J hb hx hy
  rwa [← P.map_eq hx, ← P.map_eq hy]

 theorem injective_punctured : InjOn P.map P.punctured :=
  (P.injective hb).mono (fun _ hx => subset_closure hx.1)

 theorem injective_arcs
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    ∀ γ : A, InjOn P.map (range γ.val ∪ P.punctured) := by
  intro γ
  apply (P.injective hb).mono
  rintro x (⟨t, rfl⟩ | hx)
  · exact terminalArcSet_mapsTo_closure (hAS γ.property) hb (mem_univ t)
  · exact subset_closure hx.1

end CenteredTerminalFamily
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLevelAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the physical-domain and flagged-point counts after the
free part of a level has been excluded.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_lt_top_iff (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ < ∞ ↔ (range γ ∩ H).Finite := by
  have he : pathImageCount H γ = ((range γ ∩ H).encard : ℝ≥0∞) := by
    rw [pathImageCount, ← ENNReal.tsum_set_one]
    rw [tsum_subtype (range γ ∩ H) (fun _ : X => (1 : ℝ≥0∞))]
    simp only [Set.indicator]
  rw [he]
  constructor
  · intro h
    by_contra hn
    have hi : (range γ ∩ H).Infinite := hn
    rw [hi.encard_eq] at h
    exact (not_lt_of_ge le_rfl) h
  · intro h
    exact_mod_cast h.encard_lt_top

theorem pathImageCount_le_of_cover (H A B : Set X) (γ : C(PathTime, X))
    (hcover : ∀ x ∈ range γ ∩ H, x ∈ A ∪ B) :
    pathImageCount H γ ≤ pathImageCount A γ + pathImageCount B γ := by
  rw [pathImageCount, pathImageCount, pathImageCount, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range γ ∩ H
  · rcases hcover x hx with ha | hb
    · simp only [ite_eq_left hx, ite_eq_left (show x ∈ range γ ∩ A from ⟨hx.1, ha⟩)]
      exact le_self_add
    · simp only [ite_eq_left hx, ite_eq_left (show x ∈ range γ ∩ B from ⟨hx.1, hb⟩)]
      exact le_add_self
  · simp only [ite_eq_right hx]
    exact bot_le

theorem pathImageCount_level_le_of_no_free_hits
    (U Flags H : Set X) (γ : C(PathTime, X))
    (hfree : ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), x ∈ H) :
    pathImageCount H γ ≤ pathImageCount (U ∩ H) γ + pathImageCount (Flags ∩ H) γ := by
  apply pathImageCount_le_of_cover
  intro x hx
  by_cases hu : x ∈ U
  · exact Or.inl ⟨hu, hx.2⟩
  · by_cases hf : x ∈ Flags
    · exact Or.inr ⟨hf, hx.2⟩
    · exact (hfree ⟨x, ⟨hx.1, hu, hf⟩, hx.2⟩).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteFreeCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a finite level intersection, equality with the counts in two
disjoint paid pieces leaves no additional free point.
-/

open Set Function
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_eq_encard (H : Set X) (γ : C(PathTime, X)) :
    pathImageCount H γ = ((range γ ∩ H).encard : ℝ≥0∞) := by
  rw [pathImageCount, ← ENNReal.tsum_set_one,
    tsum_subtype (range γ ∩ H) (fun _ : X => (1 : ℝ≥0∞))]
  simp only [Set.indicator]

theorem pathImageCount_union_of_disjoint {A B : Set X} (hAB : Disjoint A B)
    (γ : C(PathTime, X)) :
    pathImageCount (A ∪ B) γ = pathImageCount A γ + pathImageCount B γ := by
  rw [pathImageCount, pathImageCount, pathImageCount, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  have hh : ¬ (x ∈ A ∧ x ∈ B) := fun h => disjoint_left.mp hAB h.1 h.2
  by_cases hr : x ∈ range γ <;> by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp_all only [mem_inter_iff, mem_union, ite_true, if_true, ite_false, if_false, and_true, and_false,
      or_true, or_false, add_zero, zero_add,
      not_true_eq_false, not_false_eq_true, and_self]

theorem no_free_hits_of_finite_count_le
    (U Flags H : Set X) (hdisj : Disjoint U Flags) (γ : C(PathTime, X))
    (hfinite : pathImageCount H γ < ∞)
    (hcount : pathImageCount H γ ≤ pathImageCount (U ∩ H) γ + pathImageCount (Flags ∩ H) γ) :
    ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), x ∈ H := by
  let A := range γ ∩ H
  let B := range γ ∩ ((U ∩ H) ∪ (Flags ∩ H))
  have hA : A.Finite := (pathImageCount_lt_top_iff H γ).mp hfinite
  have hBA : B ⊆ A := by
    rintro x ⟨hx, h | h⟩ <;> exact ⟨hx, h.2⟩
  have hbcount : pathImageCount H γ ≤ pathImageCount ((U ∩ H) ∪ (Flags ∩ H)) γ := by
    rw [pathImageCount_union_of_disjoint (hdisj.mono inter_subset_left inter_subset_left)]
    exact hcount
  have hcard : A.encard ≤ B.encard := by
    rw [pathImageCount_eq_encard, pathImageCount_eq_encard] at hbcount
    exact_mod_cast hbcount
  have heq : B = A := hA.eq_of_subset_of_encard_le' hBA hcard
  rintro ⟨x, ⟨hx, hu, hf⟩, hxH⟩
  have hxB : x ∈ B := heq.symm ▸ (show x ∈ A from ⟨hx, hxH⟩)
  rcases hxB.2 with h | h
  · exact hu h.1
  · exact hf h.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteTupleLevelLaws
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The single-level conclusions pass to each finite prior union, with
its actual product Haar law and the sum of the expected counts.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem pathImageCount_iUnion_le_sum {n : ℕ} (H : Fin n → Set X)
    (γ : C(PathTime, X)) :
    pathImageCount (⋃ i, H i) γ ≤ ∑ i, pathImageCount (H i) γ := by
  simpa only [pathImageCount_eq_encard, ENNReal.tsum_set_one, ← inter_iUnion] using
    (ENNReal.tsum_iUnion_le (fun _ : X => (1 : ℝ≥0∞)) (fun i => range γ ∩ H i))

local instance localInst_rbedb44_3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩
theorem ae_finite_tuple_level_law {n : ℕ}
    (H : Fin n → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (Free : Set X) {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hgood : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H i} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ Free, (t, x) ∈ H i) :
    ∀ᵐ t ∂(Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))),
      (∫⁻ z, pathImageCount (⋃ i, {x | (t i, x) ∈ H i}) (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z),
        ¬ ∃ x ∈ range (γmap z) ∩ Free, x ∈ ⋃ i, {x | (t i, x) ∈ H i} := by
  have hall : ∀ᵐ t ∂(Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))),
      ∀ i, (∫⁻ z, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z)) < ∞ ∧
        ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ Free, (t i, x) ∈ H i :=
    ae_all_iff.mpr fun i => (measurePreserving_eval
      (fun _ : Fin n => (volume : Measure UnitAddCircle)) i).quasiMeasurePreserving.ae (hgood i)
  filter_upwards [hall] with t ht
  constructor
  · have hc (i : Fin n) : Measurable (fun z => pathImageCount {x | (t i, x) ∈ H i} (γmap z)) :=
      (measurable_pathImageCount ((hH i).preimage (continuous_const.prodMk continuous_id))).comp hγmap
    apply (show (∫⁻ z, pathImageCount (⋃ i, {x | (t i, x) ∈ H i}) (γmap z) ∂(P : Measure Z)) ≤
        ∑ i, ∫⁻ z, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z) from ?_).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ => (ht i).1)
    calc
      _ ≤ ∫⁻ z, ∑ i, pathImageCount {x | (t i, x) ∈ H i} (γmap z) ∂(P : Measure Z) :=
        lintegral_mono fun z => pathImageCount_iUnion_le_sum _ (γmap z)
      _ = _ := lintegral_finsetSum _ (fun i _ => hc i)
  · filter_upwards [ae_all_iff.mpr (fun i => (ht i).2)] with z hz
    rintro ⟨x, hx, hmem⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    exact hz i ⟨x, hx, hi⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveCodeLaw
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved outputs retained at one stage of the endpoint-law recursion.
The candidate includes actual densities and quantitative mark budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

namespace RecursiveCodeLaw

variable {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
  (L : RecursiveCodeLaw base π flags ω)

local instance localInst_rbedb44_4 : BorelSpace Sphere := ⟨rfl⟩
theorem density_measurable : Measurable L.density := (Classical.choose_spec L.candidate.1.2).1

theorem occupation_eq : meanCodeOccupation L.data L.law = sphericalArea.withDensity L.density :=
  (Classical.choose_spec L.candidate.1.2).2.1

theorem density_energy_finite : (∫⁻ x, L.density x ^ 2 ∂sphericalArea) < ∞ :=
  (Classical.choose_spec L.candidate.1.2).2.2.trans_lt L.energy_finite

variable [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem tuple_absolutelyContinuous : meanCodeTuple L.data L.law ≪ tupleReference ω := by
  obtain ⟨q, _, hq, _⟩ := L.candidate.2.2.2
  rw [hq]
  exact withDensity_absolutelyContinuous _ _

theorem flag_visit_norm_finite (i : ℕ) (hflags : support (base.levelWeights i) ⊆ flags) :
    countingSquareNorm (fun x : support (base.levelWeights i) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ :=
  (candidate_visit_norm_on_marks L.data L.law L.presentation.marks _
    (hflags.trans L.presentation.extra_marks) L.candidate.2.1).trans_lt L.visitConstant_finite

end RecursiveCodeLaw
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FlagIntersectionCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flagged intersections count each image point once. Tonelli bounds
these actual counts by the level-band width times its hit probability,
so repeated visits introduce no extra factor in the final bound. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem pathImageCount_inter_eq_tsum (S T : Set X) (γ : C(PathTime, X)) :
    pathImageCount (S ∩ T) γ =
      ∑' x : S, if x.val ∈ range γ ∩ T then (1 : ℝ≥0∞) else 0 := by
  classical
  rw [pathImageCount]
  symm
  rw [tsum_subtype S (fun x => if x ∈ range γ ∩ T then (1 : ℝ≥0∞) else 0)]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteFlagIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable flags contribute finitely many distinct intersections
for almost every independently chosen level. Repeated visits are paid
only through the actual path law's square bound.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_flag_intersection_count
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) :
    Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (S ∩ {x | (p.2, x) ∈ H}) p.1) := by
  let : Countable S := hS.to_subtype
  simp_rw [pathImageCount_inter_eq_tsum]
  apply Measurable.tsum
  intro x
  apply measurable_const.piecewise _ measurable_const
  exact (((isClosed_paths_hitting x.val).preimage continuous_fst).inter
    (hH.preimage (continuous_snd.prodMk continuous_const))).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableClosedLevelCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint Borel measurability of distinct path intersections with a
countable union of closed level relations. Paths may retrace themselves.
-/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X T : Type*} [MetricSpace X]
  [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
private theorem isClosed_indexedSeparatedHits
    {H : ℕ → Set (X × T)} (hH : ∀ n, IsClosed (H n))
    (n : ℕ) (a : Fin n → ℕ) (r : ℝ) : IsClosed (indexedSeparatedHits H n a r) := by
  let E : Set ((C(PathTime, X) × T) × (Fin n → PathTime)) :=
    {p | (∀ i j, i ≠ j → r ≤ dist (p.1.1 (p.2 i)) (p.1.1 (p.2 j))) ∧
      ∀ i, (p.1.1 (p.2 i), p.1.2) ∈ H (a i)}
  have he (i : Fin n) : Continuous
      (fun p : (C(PathTime, X) × T) × (Fin n → PathTime) => p.1.1 (p.2 i)) :=
    continuous_eval.comp (continuous_fst.fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hE : IsClosed E := by
    have hs : IsClosed {p : (C(PathTime, X) × T) × (Fin n → PathTime) |
        ∀ i j, i ≠ j → r ≤ dist (p.1.1 (p.2 i)) (p.1.1 (p.2 j))} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le continuous_const ((he i).dist (he j))
    have hm : IsClosed {p : (C(PathTime, X) × T) × (Fin n → PathTime) |
        ∀ i, (p.1.1 (p.2 i), p.1.2) ∈ H (a i)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i => (hH (a i)).preimage ((he i).prodMk continuous_fst.snd)
    exact hs.inter hm
  have hp : Prod.fst '' E = indexedSeparatedHits H n a r := by
    ext p
    constructor
    · rintro ⟨⟨_, s⟩, hs, rfl⟩
      exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨(p, s), hs, rfl⟩
  rw [← hp]
  exact isClosedMap_fst_of_compactSpace E hE

theorem measurable_countable_closed_relation_path_count
    {H : ℕ → Set (X × T)} (hH : ∀ n, IsClosed (H n)) :
    Measurable (fun p : C(PathTime, X) × T =>
      pathImageCount {x | ∃ n, (x, p.2) ∈ H n} p.1) := by
  simp_rw [pathImageCount_eq_iSup]
  apply Measurable.iSup
  intro n
  apply measurable_const.piecewise _ measurable_const
  have he : {p : C(PathTime, X) × T |
      p.1 ∈ imageHitAtLeast {x | ∃ n, (x, p.2) ∈ H n} n} =
      ⋃ a : Fin n → ℕ, ⋃ m : ℕ, indexedSeparatedHits H n a (1 / ((m : ℝ) + 1)) := by
    ext p
    constructor
    · rintro ⟨s, hs, hmem⟩
      choose a ha using hmem
      obtain ⟨m, hm⟩ := exists_reciprocal_separation (p.1 ∘ s) hs
      exact mem_iUnion₂.mpr ⟨a, m, s, hm, ha⟩
    · intro hp
      obtain ⟨a, m, s, hsep, ha⟩ := mem_iUnion₂.mp hp
      refine ⟨s, ?_, fun i => ⟨a i, ha i⟩⟩
      intro i j hij
      by_contra hne
      have h := hsep i j hne
      change p.1 (s i) = p.1 (s j) at hij
      rw [hij, dist_self] at h
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  change MeasurableSet {p : C(PathTime, X) × T |
    p.1 ∈ imageHitAtLeast {x | ∃ n, (x, p.2) ∈ H n} n}
  rw [he]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun m =>
    (isClosed_indexedSeparatedHits hH n a (1 / ((m : ℝ) + 1))).measurableSet

theorem measurable_sigmaCompact_restricted_relation_path_count
    {A : Set X} (hA : IsSigmaCompact A) {H : Set (X × T)} (hH : IsClosed H) :
    Measurable (fun p : C(PathTime, X) × T =>
      pathImageCount (A ∩ {x | (x, p.2) ∈ H}) p.1) := by
  obtain ⟨K, hK, hcover⟩ := hA
  let R : ℕ → Set (X × T) := fun n => (K n ×ˢ univ) ∩ H
  have hR (n : ℕ) : IsClosed (R n) := ((hK n).isClosed.prod isClosed_univ).inter hH
  have hs (t : T) : {x | ∃ n, (x, t) ∈ R n} = A ∩ {x | (x, t) ∈ H} := by
    ext x
    change (∃ n, (x ∈ K n ∧ t ∈ (univ : Set T)) ∧ (x, t) ∈ H) ↔ _
    rw [← hcover]
    simp only [mem_univ, and_true, mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_and_right]
  simpa only [hs] using measurable_countable_closed_relation_path_count hR

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MappedGenericLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the level-first estimates between a coded probability law,
its actual path law, and a supported subtype law. -/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem map_generic_levels
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z),
        ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ
        ∂(P.map (f := γmap) (by first | exact hγmap.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(P.map (f := γmap) (by first | exact hγmap.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  filter_upwards [hgeneric] with t ht
  have hm : Measurable (fun γ : C(PathTime, X) => pathImageCount {x | (t, x) ∈ H} γ) :=
    hfull.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hd := hdom.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hb := hflag.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hp : MeasurableSet {γ : C(PathTime, X) |
      pathImageCount {x | (t, x) ∈ H} γ < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} γ ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) γ +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) γ} :=
    (measurableSet_lt hm measurable_const).inter (measurableSet_le hm (hd.add hb))
  have hsource : ∀ᵐ z ∂(P : Measure Z),
      pathImageCount {x | (t, x) ∈ H} (γmap z) < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} (γmap z) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) := by
    filter_upwards [ht.2, ae_lt_top (hm.comp hγmap) ht.1.ne] with z hz hfin
    exact ⟨hfin, pathImageCount_level_le_of_no_free_hits U Flags _ (γmap z) hz⟩
  have hmap : ∀ᵐ γ : C(PathTime, X) ∂(P.map (f := γmap) (by first | exact hγmap.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} γ < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} γ ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) γ +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hγmap.aemeasurable hp).mpr hsource
  refine ⟨?_, hmap.mono fun γ hγ =>
    no_free_hits_of_finite_count_le U Flags _ hdisj γ hγ.1 hγ.2⟩
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map' hm.aemeasurable hγmap.aemeasurable]
  exact ht.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleBranchEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed principal branch is globally bounded, is smooth away from
its cut, and has precisely the intrinsic circle differential there.
Thus a local branch consumes only the original coordinate's energy. -/

open Set Filter Function MeasureTheory
open scoped Topology ENNReal ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem smooth_circleBranch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) {A : Set E} (hA : A ⊆ U)
    (hcut : ∀ x ∈ A, f x ≠ (a : UnitAddCircle)) :
    ContDiffOn ℝ ∞ (circleBranch f a) A :=
  fun x hx => (hf x (hA hx) a (hcut x hx)).contDiffWithinAt

theorem fderiv_circleBranch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) {x : E} (hx : x ∈ U) (hcut : f x ≠ (a : UnitAddCircle)) :
    fderiv ℝ (circleBranch f a) x = circleFDeriv f x := by
  have hb := (hf x hx a hcut).continuousAt
  have hc : ContinuousAt f x := by
    have hp := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hb
    change ContinuousAt (fun y => (circleBranch f a y : UnitAddCircle)) x at hp
    exact hp.congr (Eventually.of_forall (coe_circleBranch f a))
  exact (circleFDeriv_eq_lift hc hb (Eventually.of_forall (coe_circleBranch f a))).symm

theorem circleBranch_energy_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {f : E → UnitAddCircle} {U A : Set E} (hf : SmoothCircleOn f U)
    (a : ℝ) (hAm : MeasurableSet A) (hA : A ⊆ U)
    (hcut : ∀ x ∈ A, f x ≠ (a : UnitAddCircle))
    (μ : Measure E) :
    (∫⁻ x in A, ENNReal.ofReal ‖fderiv ℝ (circleBranch f a) x‖ ^ 2 ∂μ) ≤
      ∫⁻ x in U, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
  calc
    _ = ∫⁻ x in A, ENNReal.ofReal ‖circleFDeriv f x‖ ^ 2 ∂μ := by
      apply setLIntegral_congr_fun hAm
      intro x hx
      dsimp only
      rw [fderiv_circleBranch hf a (hA hx) (hcut x hx)]
    _ ≤ _ := lintegral_mono_set hA

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleWeightedCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two fixed cuts reduce the weighted-length estimate for a smooth
circle coordinate to the published scalar coarea specialization. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 local instance localInst_rbedb44_5 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_finite_spherical_circle_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    {D : Set ℂ} (hD : IsOpen D) {u : ℂ → UnitAddCircle} (hu : SmoothCircleOn u D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv u z‖ ^ 2) < ∞)
    (A : UnitAddCircle → Set Sphere)
    (hA : ∀ θ, ((↑) : ℂ → Sphere) ⁻¹' A θ ⊆ D ∩ {z | u z = θ})
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in A θ, g p ∂(μH[1] : Measure Sphere)) < ∞ := by
  let O (a : ℝ) := D ∩ u ⁻¹' ({(a : UnitAddCircle)}ᶜ)
  let S (a : ℝ) (θ : UnitAddCircle) : Set Sphere :=
    ((↑) : ℂ → Sphere) '' (O a ∩ {z | (circleBranch u a z : UnitAddCircle) = θ})
  have hO (a : ℝ) : IsOpen (O a) :=
    hu.continuousOn.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl
  have hcut (a : ℝ) : ∀ z ∈ O a, u z ≠ (a : UnitAddCircle) := fun _ hz => hz.2
  have hs (a : ℝ) : ContDiffOn ℝ 1 (circleBranch u a) (O a) :=
    (smooth_circleBranch hu a inter_subset_left (hcut a)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he (a : ℝ) : (∫⁻ z in O a, ENNReal.ofReal (‖fderiv ℝ (circleBranch u a) z‖ ^ 2)) < ∞ := by
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    exact (circleBranch_energy_le hu a (hO a).measurableSet inter_subset_left (hcut a) volume).trans_lt henergy
  have hpre (a : ℝ) (θ : UnitAddCircle) : ((↑) : ℂ → Sphere) ⁻¹' S a θ =
      O a ∩ {z | (circleBranch u a z : UnitAddCircle) = θ} :=
    Set.preimage_image_eq _ OnePoint.coe_injective
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  have hfinite (a : ℝ) := ae_finite_spherical_weighted_levels hcoarea hC hderiv
    (hO a) (hs a) (he a) (S a) (hpre a) g hg hg2
  have hneq : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro h
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hh).mp h
    norm_num at heq
  have hsub (θ : UnitAddCircle) : A θ ⊆ S 0 θ ∪ S (1 / 2) θ ∪ {OnePoint.infty} := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      have hz : z ∈ D ∧ u z = θ := hA θ hp
      by_cases h0 : u z ≠ (0 : UnitAddCircle)
      · exact Or.inl (Or.inl ⟨z, ⟨⟨hz.1, h0⟩, by simpa only [Set.mem_ofPred_eq, coe_circleBranch] using hz.2⟩, rfl⟩)
      · have hh : u z ≠ ((1 / 2 : ℝ) : UnitAddCircle) :=
          fun h => hneq ((not_not.mp h0).symm.trans h)
        exact Or.inl (Or.inr ⟨z, ⟨⟨hz.1, hh⟩, by simpa only [Set.mem_ofPred_eq, coe_circleBranch] using hz.2⟩, rfl⟩)
  filter_upwards [hfinite 0, hfinite (1 / 2)] with θ h0 hh
  apply lt_of_le_of_lt (lintegral_mono_set (hsub θ))
  apply lt_of_le_of_lt (lintegral_union_le g _ _)
  let := Measure.nullSingletonClass_hausdorff Sphere (by norm_num : (0 : ℝ) < 1)
  have hz : (∫⁻ p in ({OnePoint.infty} : Set Sphere), g p ∂(μH[1] : Measure Sphere)) = 0 := by
    simp
  rw [hz, add_zero]
  exact (lintegral_union_le g _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨h0, hh⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MappedPointAvoidance
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point avoidance passes to the actual compact disk-arc image law.
Injectivity is required only on each sampled arc together with the
single point under consideration. -/

open Set Function Filter MeasureTheory

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem mapped_arc_point_avoidance
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val) :
    ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K), F x ∉ range γ.val := by
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff hf.aemeasurable ?_).mpr
  · filter_upwards [hmiss] with γ hγ
    rintro ⟨t, ht⟩
    apply hγ
    refine ⟨t, ?_⟩
    apply hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x))
    simpa only [mem_preimage, hmap γ, ContinuousMap.comp_apply] using ht
  · exact ((isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe).compl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LogarithmicCutCharts
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two explicit argument cuts give local logarithmic branches on any
topological source of a continuous punctured-disk map. No local
connectedness of the source is needed for this chart construction. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem logarithmicCutChart_nonneg (a : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (logarithmicCutChart a w).im := by
  change 0 ≤ (((AddCircle.equivIco (1 : ℝ) a (normalizedArgument w) : ℝ) : ℂ) +
    ((-Real.log ‖w‖ : ℝ) : ℂ) * Complex.I).im
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add] using neg_nonneg.mpr (Real.log_nonpos (norm_nonneg w) hw)

theorem logarithmicCutChart_projection (a : ℝ) {w : ℂ} (hw : w ≠ 0) :
    diskRayProjection (logarithmicCutChart a w) = w := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    simp only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, neg_neg]
    exact Real.exp_log (norm_pos_iff.mpr hw)
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection (logarithmicCutChart a w)) =
      normalizedArgument w
    rw [diskRayProjection_argument]
    simp only [logarithmicCutChart, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    exact AddCircle.coe_equivIco

theorem continuousAt_logarithmicCutChart (a : ℝ) {w : ℂ} (hw : w ≠ 0)
    (ha : normalizedArgument w ≠ (a : UnitAddCircle)) :
    ContinuousAt (logarithmicCutChart a) w := by
  have hangle := continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) a ha).comp
      (continuousAt_normalizedArgument hw))
  exact (Complex.continuous_ofReal.continuousAt.comp hangle).add
    ((Complex.continuous_ofReal.continuousAt.comp
      ((continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr hw)).neg)).mul_const _)

theorem isOpen_logarithmicCutDomain {X : Type*} [TopologicalSpace X]
    (F : X → ℂ) (hF : Continuous F) {S : Set X} (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (a : ℝ) : IsOpen (logarithmicCutDomain F S a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have harg : ContinuousAt (fun y => normalizedArgument (F y)) x :=
    (continuousAt_normalizedArgument (h0 x hx.1)).comp hF.continuousAt
  exact inter_mem (hS.mem_nhds hx.1)
    (harg.eventually (isOpen_ne.mem_nhds hx.2))

theorem logarithmicCutDomain_cover {X : Type*} (F : X → ℂ) (S : Set X) :
    S ⊆ logarithmicCutDomain F S 0 ∪ logarithmicCutDomain F S (1 / 2) := by
  intro x hx
  by_cases h : normalizedArgument (F x) = (0 : UnitAddCircle)
  · right
    refine ⟨hx, ?_⟩
    rw [h]
    intro he
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (0 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)
      (show (1 / 2 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)).mp he
    norm_num at hh
  · exact Or.inl ⟨hx, h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LiftedMeanBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dust-band estimates for the same local representative used in the
Sobolev construction. The lift only needs nonnegative height on the domain. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem continuous_upperHalfPlaneClamp : Continuous upperHalfPlaneClamp :=
  (Complex.equivRealProdCLM.symm.continuous.comp
    (Complex.continuous_re.prodMk (Complex.continuous_im.max continuous_const))).subtype_mk _

 theorem upperHalfPlaneClamp_val {z : ℂ} (hz : 0 ≤ z.im) :
    (upperHalfPlaneClamp z).val = z :=
  Complex.ext rfl (max_eq_left hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlaneDiskInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse Cayley coordinate on the punctured closed disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem diskHalfPlane_den_ne_zero {w : ℂ} (hw : w ≠ 1) : 1 - w ≠ 0 := by
  exact sub_ne_zero.mpr hw.symm

theorem diskHalfPlane_add_I {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I = (2 * Complex.I) / (1 - w) := by
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_add_I_ne_zero {w : ℂ} (hw : w ≠ 1) :
    diskHalfPlane w + Complex.I ≠ 0 := by
  rw [diskHalfPlane_add_I hw]
  exact div_ne_zero (by simp) (diskHalfPlane_den_ne_zero hw)

theorem halfPlaneDisk_diskHalfPlane {w : ℂ} (hw : w ≠ 1) :
    halfPlaneDisk (diskHalfPlane w) = w := by
  rw [halfPlaneDisk, div_eq_iff (diskHalfPlane_add_I_ne_zero hw)]
  unfold diskHalfPlane
  field_simp [diskHalfPlane_den_ne_zero hw]
  ring

theorem diskHalfPlane_halfPlaneDisk {z : ℂ} (hz : 0 ≤ z.im) :
    diskHalfPlane (halfPlaneDisk z) = z := by
  rw [diskHalfPlane, div_eq_iff (diskHalfPlane_den_ne_zero (halfPlaneDisk_ne_one hz))]
  unfold halfPlaneDisk
  field_simp [halfPlaneDisk_den_ne_zero hz]
  ring

theorem diskHalfPlane_nonneg {w : ℂ} (hw : w ≠ 1) (hn : ‖w‖ ≤ 1) :
    0 ≤ (diskHalfPlane w).im := by
  have hh : ‖halfPlaneDisk (diskHalfPlane w)‖ ≤ 1 := by rw [halfPlaneDisk_diskHalfPlane hw]; exact hn
  rw [halfPlaneDisk, norm_div] at hh
  have hb : ‖diskHalfPlane w - Complex.I‖ ≤ ‖diskHalfPlane w + Complex.I‖ :=
    (div_le_one (norm_pos_iff.mpr (diskHalfPlane_add_I_ne_zero hw))).mp hh
  have hs := halfPlaneDisk_normSq (diskHalfPlane w)
  simp only [← Complex.sq_norm] at hs
  nlinarith [norm_nonneg (diskHalfPlane w - Complex.I)]

theorem continuousOn_diskHalfPlane : ContinuousOn diskHalfPlane {w : ℂ | w ≠ 1} :=
  (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn (fun _ h => diskHalfPlane_den_ne_zero h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_HalfPlanePathSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The side path test in the original half-plane coordinates. -/

open Set Function Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem HalfPlaneRay.diskAvoiding_iff_halfPlaneAvoiding (R : HalfPlaneRay)
    {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    DiskAvoidingPath R.crosscut.toContinuousMap (halfPlaneDisk z) (halfPlaneDisk w) ↔
      HalfPlaneAvoidingPath R z w := by
  constructor
  · rintro ⟨δ, h0, h1, hδ⟩
    have hne : ∀ t, δ t ≠ 1 := by
      intro t ht
      apply (hδ t).2
      exact ⟨⊤, R.compactify_top.trans ht.symm⟩
    let ε : C(PathTime, ℂ) := ⟨diskHalfPlane ∘ δ,
      continuousOn_diskHalfPlane.comp_continuous δ.continuous hne⟩
    refine ⟨ε, ?_, ?_, ?_⟩
    · change diskHalfPlane (δ 0) = z
      rw [h0, diskHalfPlane_halfPlaneDisk hz]
    · change diskHalfPlane (δ 1) = w
      rw [h1, diskHalfPlane_halfPlaneDisk hw]
    · intro t
      have hn : ‖δ t‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using (hδ t).1
      refine ⟨diskHalfPlane_nonneg (hne t) hn, ?_⟩
      rintro ⟨s, hs⟩
      apply (hδ t).2
      have he : δ t = halfPlaneDisk (R.curve s) := by
        rw [← halfPlaneDisk_diskHalfPlane (hne t)]
        exact congrArg halfPlaneDisk hs.symm
      rw [he]
      exact (R.cayley_mem_crosscut_iff (R.nonneg s)).mpr (mem_range_self s)
  · rintro ⟨δ, h0, h1, hδ⟩
    let ε : C(PathTime, ℂ) := ⟨halfPlaneDisk ∘ δ,
      continuousOn_halfPlaneDisk.comp_continuous δ.continuous (fun t => (hδ t).1)⟩
    refine ⟨ε, congrArg halfPlaneDisk h0, congrArg halfPlaneDisk h1, ?_⟩
    intro t
    refine ⟨Metric.mem_closedBall.mpr ?_, ?_⟩
    · simpa only [ε, ContinuousMap.coe_mk, Function.comp_apply, dist_zero_right] using
        halfPlaneDisk_norm_le (hδ t).1
    · exact fun hm => (hδ t).2 ((R.cayley_mem_crosscut_iff (hδ t).1).mp hm)

 theorem HalfPlaneRay.right_iff_halfPlanePath (hsep : UnitDiskCrosscutSeparation)
    (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) {z : ℂ} (hz : 0 ≤ z.im) :
    halfPlaneDisk z ∉ closure (jordanInterior H) ↔ HalfPlaneAvoidingPath R z
      (((R.curve ⟨0, bot_lt_top⟩).re + 1 : ℝ) : ℂ) := by
  rw [R.right_iff_avoidingPath hsep hH
    (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using halfPlaneDisk_norm_le hz))]
  exact R.diskAvoiding_iff_halfPlaneAvoiding hz (by simp)

 theorem HalfPlaneRay.translated_right (hsep : UnitDiskCrosscutSeparation)
    (R S : HalfPlaneRay) {H J : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) (hJ : S.IsJordan J)
    (a : ℝ) (ha : ∀ t, S.curve t = R.curve t + (a : ℂ))
    {z : ℂ} (hz : 0 ≤ z.im) (hr : halfPlaneDisk z ∉ closure (jordanInterior H)) :
    halfPlaneDisk (z + (a : ℂ)) ∉ closure (jordanInterior J) := by
  have hza : 0 ≤ (z + (a : ℂ)).im := by simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz
  apply (S.right_iff_halfPlanePath hsep hJ hza).mpr
  obtain ⟨δ, h0, h1, hδ⟩ := (R.right_iff_halfPlanePath hsep hH hz).mp hr
  refine ⟨⟨fun t => δ t + (a : ℂ), δ.continuous.add continuous_const⟩,
    congrArg (fun w => w + (a : ℂ)) h0, ?_, ?_⟩
  · change δ 1 + (a : ℂ) = _
    rw [h1, ha, Complex.add_re, Complex.ofReal_re]
    push_cast
    ring
  · intro t
    refine ⟨?_, ?_⟩
    · simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.ofReal_im, add_zero] using (hδ t).1
    · rintro ⟨s, hs⟩
      rw [ha s] at hs
      exact (hδ t).2 ⟨s, add_right_cancel hs⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricIndexPeriod
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deck translation adds the corresponding integer to the actual ray
index and hence to its expectation. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem translatedHalfPlaneRay_curve_add (γ : C(PathTime, ℂ))
    (hγ : γ ∈ diskTerminalArcSet) (k n : ℤ) (t : DiskRayTime) :
    (translatedHalfPlaneRay γ hγ (k + n)).curve t =
      (translatedHalfPlaneRay γ hγ k).curve t + (n : ℂ) := by
  change diskRayComplex γ hγ.1 hγ.2.2.1 t + ((k + n : ℤ) : ℂ) =
    (diskRayComplex γ hγ.1 hγ.2.2.1 t + (k : ℂ)) + (n : ℂ)
  rw [Int.cast_add, add_assoc]

 theorem rayRightIndices_translate_iff (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (k n : ℤ) :
    k + n ∈ rayRightIndices hsch γ hγ (z + (n : ℂ)) ↔ k ∈ rayRightIndices hsch γ hγ z := by
  constructor
  · intro hm
    have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ (k + n)) (translatedHalfPlaneRay γ hγ k)
      (rayJordan_spec hsch γ hγ (k + n)) (rayJordan_spec hsch γ hγ k)
      (-(n : ℝ)) (fun t => by
        rw [translatedHalfPlaneRay_curve_add]
        push_cast
        simp only [add_neg_cancel_right]) hza hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_neg, Complex.ofReal_intCast,
      add_neg_cancel_right] using hh
  · intro hm
    have hh := HalfPlaneRay.translated_right hsep
      (translatedHalfPlaneRay γ hγ k) (translatedHalfPlaneRay γ hγ (k + n))
      (rayJordan_spec hsch γ hγ k) (rayJordan_spec hsch γ hγ (k + n))
      (n : ℝ) (fun t => by simpa only [Complex.ofReal_intCast] using
        translatedHalfPlaneRay_curve_add γ hγ k n t) hz hm
    simpa only [rayRightIndices, mem_ofPred_eq, Complex.ofReal_intCast] using hh

 theorem geometricRayIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ℂ) (hz : 0 ≤ z.im) (n : ℤ) :
    geometricRayIndex hsch γ hγ (z + (n : ℂ)) = geometricRayIndex hsch γ hγ z + n := by
  have hza : 0 ≤ (z + (n : ℂ)).im := by simpa only [Complex.add_im, Complex.intCast_im, add_zero] using hz
  have h0 := geometricRayIndex_isGreatest hsch γ hγ z hz
  have h1 := geometricRayIndex_isGreatest hsch γ hγ (z + (n : ℂ)) hza
  apply le_antisymm
  · have hm : geometricRayIndex hsch γ hγ (z + (n : ℂ)) - n ∈ rayRightIndices hsch γ hγ z := by
      apply (rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mp
      simpa only [sub_add_cancel] using h1.1
    have hb := h0.2 hm
    omega
  · exact h1.2 ((rayRightIndices_translate_iff hsch hsep γ hγ z hz _ n).mpr h0.1)

 theorem meanGeometricIndex_translate (hsch : PlanarSchoenflies)
    (hsep : UnitDiskCrosscutSeparation) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (n : ℤ) :
    meanGeometricIndex hsch K hKS η (z.translate n) = meanGeometricIndex hsch K hKS η z + (n : ℝ) := by
  have hi := integrable_geometricRayIndex hsch hsep K hK hKS η z
  simp only [meanGeometricIndex, ClosedUpperHalfPlane.translate,
    geometricRayIndex_translate hsch hsep _ _ _ z.property, Int.cast_add,
    integral_add hi (integrable_const (n : ℝ)), integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, one_smul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanIndexCircle
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mean index descends through the logarithmic cover to a
circle-valued coordinate. Every continuous local lift represents the
same coordinate; no choice of branch is part of the resulting map. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem diskRayProjection_eq_implies_translate
    (z w : ClosedUpperHalfPlane) (h : diskRayProjection z.val = diskRayProjection w.val) :
    ∃ n : ℤ, z = w.translate n := by
  have hi : z.val.im = w.val.im := by
    have hn := congrArg norm h
    rw [diskRayProjection_norm, diskRayProjection_norm] at hn
    have he := Real.exp_injective hn
    linarith
  have hr : (z.val.re : UnitAddCircle) = (w.val.re : UnitAddCircle) := by
    simpa only [diskRayProjection_argument] using congrArg normalizedArgument h
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 z.val.re w.val.re).mp hr
  refine ⟨n, Subtype.ext ?_⟩
  apply Complex.ext
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_re, Complex.intCast_re, mul_one] using hn
  · simpa only [ClosedUpperHalfPlane.translate, Complex.add_im, Complex.intCast_im, add_zero] using hi

 theorem meanGeometricIndex_mod_eq_of_projection_eq
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z w : ClosedUpperHalfPlane)
    (h : diskRayProjection z.val = diskRayProjection w.val) :
    (meanGeometricIndex hsch K hKS η z : UnitAddCircle) =
      (meanGeometricIndex hsch K hKS η w : UnitAddCircle) := by
  obtain ⟨n, rfl⟩ := diskRayProjection_eq_implies_translate z w h
  apply (addCircle_eq_iff_exists_int 1 _ _).mpr
  exact ⟨n, by simpa only [mul_one] using meanGeometricIndex_translate hsch hsep K hK hKS η w n⟩

 theorem diskMeanCircle_projection
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) :
    diskMeanCircle hsch K hKS η (diskRayProjection z.val) =
      (meanGeometricIndex hsch K hKS η z : UnitAddCircle) := by
  have hex : ∃ w : ClosedUpperHalfPlane, diskRayProjection w.val = diskRayProjection z.val := ⟨z, rfl⟩
  rw [diskMeanCircle, dite_eq_left hex]
  exact meanGeometricIndex_mod_eq_of_projection_eq hsch hsep K hK hKS η
    (Classical.choose hex) z (Classical.choose_spec hex)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalBandTransitions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer changes of local sheet preserve the actual interval-band
level graph. Eventual equality is enough: values outside the patch do
not enter its boundary band. -/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

theorem clusterGraph_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ clusterGraph D g ↔ (x, t) ∈ clusterGraph D f := by
  simp only [mem_clusterGraph_iff_mapClusterPt]
  constructor
  · intro ht
    have h := (ht.congrFun heq).continuousAt_comp
      (continuousAt_id.sub_const c)
    simpa only [Function.comp_def, id_eq, add_sub_cancel_right] using h
  · intro ht
    have h := ht.continuousAt_comp (continuousAt_id.add_const c)
    exact h.congrFun heq.symm

theorem intervalBand_add_const_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {c : ℝ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + c) (t : ℝ) :
    (x, t + c) ∈ intervalFiberHull (clusterGraph D g) ↔
      (x, t) ∈ intervalFiberHull (clusterGraph D f) := by
  constructor
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    have ha' : (x, (a - c) + c) ∈ clusterGraph D g := by simpa using ha
    have hb' : (x, (b - c) + c) ∈ clusterGraph D g := by simpa using hb
    exact mem_intervalFiberHull_iff.mpr ⟨a - c, b - c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mp ha',
      (clusterGraph_add_const_of_eventuallyEq heq _).mp hb', hs, by nlinarith [ht]⟩
  · intro ht
    obtain ⟨a, b, s, ha, hb, hs, ht⟩ := mem_intervalFiberHull_iff.mp ht
    exact mem_intervalFiberHull_iff.mpr ⟨a + c, b + c, s,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr ha,
      (clusterGraph_add_const_of_eventuallyEq heq _).mpr hb, hs, by nlinarith [ht]⟩

theorem circleBand_fiber_eq_of_eventually_add_int
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D : Set X} {f g : X → ℝ} {x : X} {k : ℤ}
    (heq : g =ᶠ[𝓝[D] x] fun y => f y + (k : ℝ)) :
    {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph D g} =
      {θ | (x, θ) ∈ circleBandGraph D f} := by
  have hadd (a : ℝ) : ((a + (k : ℝ) : ℝ) : UnitAddCircle) = (a : UnitAddCircle) :=
    unitAddCircle_eq_iff_exists_int.mpr ⟨k, rfl⟩
  ext θ
  constructor
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    have ha' : (x, (a - (k : ℝ)) + (k : ℝ)) ∈ intervalFiberHull (clusterGraph D g) := by
      simpa using ha
    refine ⟨(x, a - (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mp ha', ?_⟩
    change (x, ((a - (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    have hc := hadd (a - (k : ℝ))
    have hs : ((a - (k : ℝ) : ℝ) : UnitAddCircle) = θ := by
      have hc' : (a : UnitAddCircle) = ((a - (k : ℝ) : ℝ) : UnitAddCircle) := by
        simpa only [sub_add_cancel] using hc
      exact hc'.symm.trans (congrArg Prod.snd he)
    exact congrArg (fun θ => (x, θ)) hs
  · rintro ⟨⟨y, a⟩, ha, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    refine ⟨(x, a + (k : ℝ)), (intervalBand_add_const_of_eventuallyEq heq _).mpr ha, ?_⟩
    change (x, ((a + (k : ℝ) : ℝ) : UnitAddCircle)) = (x, θ)
    exact Prod.ext rfl ((hadd a).trans (congrArg Prod.snd he))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodBandGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The period-coordinate level graph of Definition 2.3, assembled from
local real branches on the punctured mask. The singular point belongs to
every level. Integer changes of sheet give the compatibility used below;
the closedness proof only needs the resulting equality of projected bands. -/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem periodBandGraph_on_patch {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hmiss : ∀ i, b ∉ V i)
    (hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j))
    {i : ι} {x : Sphere} (hx : x ∈ V i) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔ x ∈ M ∧ (x, θ) ∈ circleBandGraph D (f i) := by
  constructor
  · rintro ⟨hxM, rfl | ⟨j, hxj, hj⟩⟩
    · exact (hmiss i hx).elim
    · exact ⟨hxM, (hcompat j i x hxj hx θ).mp hj⟩
  · rintro ⟨hxM, hi⟩
    exact ⟨hxM, Or.inr ⟨i, hx, hi⟩⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PeriodWeightedCoarea
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked mean-period levels have finite weighted physical
length almost everywhere, as required by the subsequent barrier step. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

 local instance localInst_rbedb44_6 : BorelSpace Sphere := ⟨rfl⟩
theorem SmoothMeanPeriodData.ae_finite_weighted_levels
    (hcoarea : WeightedPlanarScalarCoarea)
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} (hG : IsOpen G) (hS : IsOpen S)
    {b : Sphere} (hbU : b ∉ U) (hMS : M \ {b} ⊆ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ p in G ∩ π ⁻¹' {x | (x, θ) ∈ periodBandGraph U M b Q.patch Q.branch},
        g p ∂(μH[1] : Measure Sphere)) < ∞ := by
  let D := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter
    (hS.preimage (hπ.comp OnePoint.continuous_coe))
  apply ae_finite_spherical_circle_weighted_levels hcoarea hD Q.physical_smooth
    Q.physical_energy _ _ g hg hg2
  intro θ z hz
  have hzU := hPU z hz.1
  have hv := (Q.domain_value (π (z : Sphere)) hzU θ).mp hz.2
  have hzS : π (z : Sphere) ∈ S := hMS ⟨hv.1, fun h => hbU (h ▸ hzU)⟩
  refine ⟨⟨hz.1, hzS⟩, ?_⟩
  change Q.physical z = θ
  rw [Q.physical_value z hz.1 hzS]
  exact hv.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PriorLevelFamily
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact weighted-level data consumed by the barrier construction.
Both earlier real coordinates and the constructed masked means supply it. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel

 local instance localInst_rbedb44_7 : BorelSpace Sphere := ⟨rfl⟩
theorem PriorLevelFamily.length
    {G : Set Sphere} {π : Sphere → Sphere} (P : PriorLevelFamily G π) (i : ℕ) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (μH[1] : Measure Sphere) (G ∩ π ⁻¹' {x | (x, θ) ∈ P.graph i}) < ∞ := by
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    P.weighted i (fun _ => 1) measurable_const (by simp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteTupleCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered compatibility null sets survive arbitrary finite selections
of a prior tuple, including tuples with repeated labels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the free set to a mask neighborhood loses no compatibility
conditions: the new period levels have no incidences outside their mask,
and their distinguished point has already been flagged. -/

open Set Function

namespace CircleDomainRigidity

theorem freeComponentFailure_inter_eq_of_support
    {X T J Λ : Type*} [TopologicalSpace X]
    (Free S : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hs : ∀ x ∈ Free, ∀ t, (x, t) ∈ Rnew → x ∈ S) :
    freeComponentFailure (Free ∩ S) Rnew R labels =
      freeComponentFailure Free Rnew R labels := by
  apply Subset.antisymm
  · rintro p ⟨⟨x, q⟩, h, rfl⟩
    exact ⟨(x, q), ⟨h.1.1, h.2⟩, rfl⟩
  · rintro p ⟨⟨x, q⟩, h, rfl⟩
    exact ⟨(x, q), ⟨⟨h.1, hs x h.1 q.1 h.2.1⟩, h.2⟩, rfl⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PerturbedMeanFreeTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a point avoided by the compact arc law, a vanishing correction
leaves a genuine mean trace. Its entire interval-band fiber is therefore
the single value used in ordered compatibility. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_perturbed_mean_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (D : Set X) (x : X) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y) :
    Tendsto u (𝓝[D] x) (𝓝 (meanGeometricIndex hsch K hKS η (L x))) := by
  have hmean := (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L x) hmiss).tendsto.comp hL
  have hsum := hmean.add hR
  simp only [add_zero] at hsum
  exact Tendsto.congr' hu.symm hsum

theorem perturbed_mean_band_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    (D : Set X) (x : X) (hx : x ∈ closure D) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y)
    {B : ℝ} (hbound : ∀ y ∈ D, |u y| ≤ B) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D u ↔
      diskMeanCircle hsch K hKS η (diskRayProjection (L x).val) = θ := by
  rw [circleBandGraph_of_trace hbound hx
    (tendsto_perturbed_mean_at_avoided_point hsch hsep K hK hKS η D x L hL hmiss u R hR hu)]
  rw [diskMeanCircle_projection hsch hsep K hK hKS η]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanPeriodFreeValues
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual period graph has the original mean value at every free
dust point avoided by the selected law. Vanishing smoothing error leaves
its limiting bands unchanged. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem period_graph_mean_free_value
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (D M S Free : Set Sphere) (hdense : Dense D) (b : Sphere) (hb : b ∉ Free)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ Free ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val)
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (f : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ D → |f i x| ≤ B i)
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, f j =ᶠ[𝓝[D] x] fun y => f i y + k)
    (R : Sphere → ℝ) (hR : ∀ x ∈ Free, Tendsto R (𝓝[D] x) (𝓝 0))
    (hf : ∀ i x, x ∈ V i → f i x =
      meanGeometricIndex hsch K hKS η (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + R x)
    (x : Sphere) (hx : x ∈ Free) (θ : UnitAddCircle) :
    (x, θ) ∈ periodBandGraph D M b V f ↔
      x ∈ M ∧ diskMeanCircle hsch K hKS η (F x) = θ := by
  by_cases hxM : x ∈ M
  · have hxb : x ≠ b := fun he => hb (he ▸ hx)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxM, hxb⟩)
    have hcompat : ∀ i j x, x ∈ V i → x ∈ V j → ∀ θ,
        (x, θ) ∈ circleBandGraph D (f i) ↔ (x, θ) ∈ circleBandGraph D (f j) := by
      intro i j x hxi hxj θ
      obtain ⟨k, hk⟩ := htrans i j x hxi hxj
      exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
    rw [periodBandGraph_on_patch D M b V f hbV hcompat hi θ]
    have hxS : x ∈ S := hVS i (subset_closure hi)
    let L : Sphere → ClosedUpperHalfPlane := fun y =>
      upperHalfPlaneClamp (logarithmicCutChart (a i) (F y))
    have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
      ((hlog i).continuousAt (mem_of_superset ((hV i).mem_nhds hi) subset_closure))
    have hproj : diskRayProjection (L x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (a i) (h1 x hxS))]
      exact logarithmicCutChart_projection (a i) (h0 x hxS)
    have havoid : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val := by
      simpa only [hproj] using hmiss x ⟨hx, hxS⟩
    have heq : f i =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y := by
      filter_upwards [nhdsWithin_le_nhds ((hV i).mem_nhds hi)] with y hy
      exact hf i y hy
    have hbnd := perturbed_mean_band_at_avoided_point hsch hsep K hK hKS η D x
      (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt havoid
      (f i) R (hR x hx) heq (hbound i) θ
    rw [hproj] at hbnd
    rw [hbnd]
  · constructor
    · exact fun h => (hxM h.1).elim
    · exact fun h => (hxM h.1).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MeanIndexNullTrace
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null free traces for the actual averaged index on a locally connected
prior level continuum. Only connected-open arc existence is supplied by
the published topological input; the intersection measure and payment
inequality are constructed here. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_index_null_trace_on_continuum
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H V Free C : Set X} (hH : IsClosed H) (hV : IsOpen V)
    (hFree : MeasurableSet Free)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hC : IsCompact C) (hCH : C ⊆ H) [LocallyConnectedSpace C]
    (harcs : HasSimpleArcsInConnectedOpens C)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (Ψ : X → ℂ) (hΨ : ContinuousOn Ψ V)
    (hpos : ∀ x ∈ V, 0 ≤ (Ψ x).im)
    (hproj : ∀ x ∈ V, diskRayProjection (Ψ x) = F x)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ V)) (hinj : InjOn F V) :
    volume ((fun x => liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ x)) ''
      (Free ∩ C ∩ V)) = 0 := by
  let u : X → ℝ := fun x => liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ x)
  let ν := meanPathIntersectionMeasure H
    ((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)
  let : IsFiniteMeasure ν := meanPathIntersectionMeasure_finite H hH _ hfinite
  have hνFree : ν Free = 0 := by
    exact meanPathIntersectionMeasure_map_null (η : Measure A) Subtype.val
      measurable_subtype_coe H hH Free hFree hmiss
  let μC : Measure C := ν.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : C → X) :=
    MeasurableEmbedding.subtype_coe hC.isClosed.measurableSet
  let : IsFiniteMeasure μC := ⟨by
    change ν.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top ν _⟩
  have hμFree : μC (Subtype.val ⁻¹' Free) = 0 := by
    rw [show μC (Subtype.val ⁻¹' Free) = ν (Subtype.val '' (Subtype.val ⁻¹' Free)) from
      hemb.comap_apply ν _]
    exact measure_mono_null (image_preimage_subset _ _) hνFree
  have hn : volume ((fun x : C => u x.val) ''
      ((Subtype.val ⁻¹' Free) ∩ (Subtype.val ⁻¹' V))) = 0 := by
    apply null_image_of_simple_arc_payment (μ := μC) harcs
      (hV.preimage continuous_subtype_val)
      (measure_mono_null inter_subset_left hμFree) (fun x : C => u x.val)
      (by norm_num : (0 : ℝ) ≤ 1)
    intro x hx y hy γ hγ hγV
    let α : Path x.val y.val := γ.map continuous_subtype_val
    have hα : Injective α := Subtype.val_injective.comp hγ
    have hαV : range α ⊆ V := by
      rintro z ⟨t, rfl⟩
      exact hγV (mem_range_self t)
    have hαH : range α ⊆ H := by
      rintro z ⟨t, rfl⟩
      exact hCH (γ t).property
    have hp := lifted_mean_index_arc_payment hsch hsep A K hK hKS η F f hf hmap
      hH hfinite Ψ hΨ hpos hproj hF hinj α.toContinuousMap hα hαV hαH
    have hr := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν (range α))).mp hp
    have hmass : μC.real (range γ) = ν.real (range α) := by
      rw [measureReal_def, measureReal_def, hemb.comap_apply]
      congr 1
      apply congrArg ν
      change Subtype.val '' range γ = range (Subtype.val ∘ γ)
      exact (range_comp _ _).symm
    rw [one_mul, hmass]
    have h0 : α.toContinuousMap 0 = x.val := α.source
    have h1 : α.toContinuousMap 1 = y.val := α.target
    rw [h0, h1, abs_sub_comm] at hr
    exact hr
  have himage : (fun x : C => u x.val) ''
      ((Subtype.val ⁻¹' Free) ∩ (Subtype.val ⁻¹' V)) = u '' (Free ∩ C ∩ V) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxF, hxV⟩, rfl⟩
      exact ⟨x.val, ⟨⟨hxF, x.property⟩, hxV⟩, rfl⟩
    · rintro ⟨x, ⟨⟨hxF, hxC⟩, hxV⟩, rfl⟩
      exact ⟨⟨x, hxC⟩, ⟨hxF, hxV⟩, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MeanCircleNullTrace
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual circle-valued mean has Haar-null free traces on each
locally connected prior continuum. Two explicit argument cuts cover the
punctured mask, so no family of local branches is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_null_trace_on_continuum
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {H S Free C : Set X} (hH : IsClosed H) (hS : IsOpen S)
    (hFree : MeasurableSet Free)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hC : IsCompact C) (hCH : C ⊆ H) [LocallyConnectedSpace C]
    (harcs : HasSimpleArcsInConnectedOpens C)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S) :
    volume ((fun x => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x)) ''
      (Free ∩ C ∩ S)) = 0 := by
  let W : ℝ → Set X := logarithmicCutDomain F S
  let Ψ : ℝ → X → ℂ := fun a x => logarithmicCutChart a (F x)
  let u : ℝ → X → ℝ := fun a x =>
    liftedMeanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ a x)
  let w : X → UnitAddCircle := fun x => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x)
  have hWS (a : ℝ) : W a ⊆ S := fun _ hx => hx.1
  have hWo (a : ℝ) : IsOpen (W a) :=
    isOpen_logarithmicCutDomain F F.continuous hS h0 a
  have hΨ (a : ℝ) : ContinuousOn (Ψ a) (W a) := by
    intro x hx
    exact ((continuousAt_logarithmicCutChart a (h0 x hx.1) hx.2).comp
      F.continuous.continuousAt).continuousWithinAt
  have hp (a : ℝ) (x : X) (hx : x ∈ W a) : 0 ≤ (Ψ a x).im :=
    logarithmicCutChart_nonneg a (h1 x hx.1)
  have hproj (a : ℝ) (x : X) (hx : x ∈ W a) : diskRayProjection (Ψ a x) = F x :=
    logarithmicCutChart_projection a (h0 x hx.1)
  have hlocal (a : ℝ) (x : X) (hx : x ∈ W a) : (u a x : UnitAddCircle) = w x := by
    dsimp only [u, w]
    rw [liftedMeanGeometricIndex_eq hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) id (Ψ a x) (hp a x hx),
      ← hproj a x hx]
    exact (diskMeanCircle_projection hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) ⟨Ψ a x, hp a x hx⟩).symm
  have hn (a : ℝ) : volume (w '' (Free ∩ C ∩ W a)) = 0 := by
    have hreal := mean_index_null_trace_on_continuum hsch hsep A K hK hKS η F f hf
      hmap hH (hWo a) hFree hmiss hC hCH harcs hfinite (Ψ a) (hΨ a) (hp a)
      (hproj a) (fun γ => (hF γ).mono (union_subset_union_right _ (hWS a)))
      (hinj.mono (hWS a))
    apply measure_mono_null ?_ (volume_addCircle_image_eq_zero hreal)
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨u a x, ⟨x, hx, rfl⟩, hlocal a x hx.2⟩
  apply measure_mono_null ?_ (measure_union_null (hn 0) (hn (1 / 2)))
  rintro _ ⟨x, ⟨⟨hxF, hxC⟩, hxS⟩, rfl⟩
  rcases logarithmicCutDomain_cover F S hxS with hx | hx
  · exact Or.inl ⟨x, ⟨⟨hxF, hxC⟩, hx⟩, rfl⟩
  · exact Or.inr ⟨x, ⟨⟨hxF, hxC⟩, hx⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MeanCircleLevelTrace
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite physical length gives the topology of a prior level union.
The actual mean-index payment then makes its free component traces null. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_null_component_traces
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B H Free S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hH : IsCompact H) (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ G) < ∞)
    (hFree : MeasurableSet Free) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H) Free)
    (hfinite : (∫⁻ γ, pathImageCount H γ
      ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S) :
    HasFiniteLargeContinuumBound H ∧
      ∀ C : Set H, (∃ x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : H => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x.val)) ''
          ((Subtype.val ⁻¹' (Free ∩ S)) ∩ C)) = 0 := by
  obtain ⟨hbound, _, hloc⟩ := level_topology_of_finite_physical_length
    π hπ hsurj hfiber hG hB hTD hdust hH hlength
  refine ⟨hbound, ?_⟩
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  rintro C ⟨x, rfl⟩ _
  let C := connectedComponent x
  have hC : IsCompact C := isClosed_connectedComponent.isCompact
  let : LocallyConnectedSpace C := hloc C hC isConnected_connectedComponent
  let D : Set X := Subtype.val '' C
  have hD : IsCompact D := hC.image continuous_subtype_val
  have hDH : D ⊆ H := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let e : C ≃ₜ D := Topology.IsEmbedding.subtypeVal.homeomorphImage C
  let : LocallyConnectedSpace D := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hn := mean_circle_null_trace_on_continuum hsch hsep A K hK hKS η F f hf hmap
    hH.isClosed hS hFree hmiss hD hDH (harcs D hD inferInstance)
    hfinite h0 h1 hF hinj
  have himage : (fun z : H => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F z.val)) ''
      ((Subtype.val ⁻¹' (Free ∩ S)) ∩ C) =
      (fun z => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F z)) '' (Free ∩ D ∩ S) := by
    ext t
    constructor
    · rintro ⟨z, ⟨⟨hzF, hzS⟩, hzC⟩, rfl⟩
      exact ⟨z.val, ⟨⟨hzF, z, hzC, rfl⟩, hzS⟩, rfl⟩
    · rintro ⟨z, ⟨⟨hzF, y, hyC, rfl⟩, hzS⟩, rfl⟩
      exact ⟨y, ⟨⟨hzF, hzS⟩, hyC⟩, rfl⟩
  rwa [himage]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanCircleCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered compatibility of the actual mean circle coordinate follows
from the generic intersection laws, finite physical prior lengths, and
its proved null traces. No compatibility of the new coordinate is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_circle_compatibility_of_generic_levels
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B Free S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hFree : MeasurableSet Free) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞ ∧
      ∀ᵐ γ : A ∂(η : Measure A),
        ¬ ∃ x ∈ range γ.val ∩ Free, (x, t) ∈ R i)
    (Rnew : Set (X × UnitAddCircle)) (hnew : IsClosed Rnew)
    (hnewlevel : ∀ x ∈ Free ∩ S, ∀ t, (x, t) ∈ Rnew ↔
      diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x) = t)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Free ∩ S) Rnew R labels) = 0 := by
  let H : (Fin n → UnitAddCircle) → Set X :=
    fun θ => {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  have hHunion (θ) : H θ = ⋃ j, {x | (x, θ j) ∈ R (labels j)} := by
    ext x
    simp [H, finiteLevelUnionGraph]
  have hcounts := ae_finite_tuple_level_law
    (fun j : Fin n => Prod.swap ⁻¹' R (labels j))
    (fun j => (hR (labels j)).preimage continuous_swap) Free η Subtype.val measurable_subtype_coe
    (fun j => (hgeneric (labels j)).mono fun t ht => by
      refine ⟨?_, ht.2⟩
      have hclosed : IsClosed {x | (x, t) ∈ R (labels j)} :=
        (hR (labels j)).preimage (continuous_id.prodMk continuous_const)
      have htfin := ht.1
      rw [ProbabilityMeasure.toMeasure_map,
        lintegral_map' (measurable_pathImageCount hclosed).aemeasurable
          measurable_subtype_coe.aemeasurable] at htfin
      exact htfin)
  have hlen := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => G ∩ π ⁻¹' {x | (x, t) ∈ R i}) (fun _ => 1) labels
    (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hlength)
  apply measure_freeComponentFailure_eq_zero hLusin n (hFree.inter hS.measurableSet)
    hnew hR labels (fun x => diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x)) hnewlevel
  filter_upwards [hcounts, hlen] with θ hc hl
  have hcompact : IsCompact (H θ) :=
    ((isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)).isCompact
  have hlengthH : (μH[1] : Measure Y) (π ⁻¹' H θ ∩ G) < ∞ := by
    have hset : (⋃ j, G ∩ π ⁻¹' {x | (x, θ j) ∈ R (labels j)}) = π ⁻¹' H θ ∩ G := by
      rw [hHunion, preimage_iUnion, inter_comm, inter_iUnion]
    simpa only [lintegral_one, Measure.restrict_apply_univ, hset] using hl
  have hfinite : (∫⁻ γ, pathImageCount (H θ) γ
      ∂((η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure C(PathTime, X)) : Measure _)) < ∞ := by
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map'
      (measurable_pathImageCount hcompact.isClosed).aemeasurable measurable_subtype_coe.aemeasurable]
    simpa only [hHunion, Prod.swap_prod_mk, mem_preimage] using hc.1
  have hmiss : ∀ᵐ γ : A ∂(η : Measure A), Disjoint (range γ.val ∩ H θ) Free := by
    filter_upwards [hc.2] with γ hγ
    apply disjoint_left.mpr
    rintro x ⟨hx, hxH⟩ hxF
    apply hγ
    refine ⟨x, ⟨hx, hxF⟩, ?_⟩
    simpa only [← hHunion, Prod.swap_prod_mk, mem_preimage] using hxH
  exact mean_circle_null_component_traces hsch hsep π hπ hsurj hfiber hG hB hTD hdust
    hcompact hlengthH hFree hS harcs A K hK hKS η F f hf hmap hmiss hfinite h0 h1 hF hinj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcGenericLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic prior levels survive measurable subarc selection and the
factor-two compact conditioning used for terminal arc laws. The free set
need not be measurable: finite Borel count inequalities carry the statement. -/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem subarc_generic_levels
    (μ η : ProbabilityMeasure C(PathTime, X))
    (f : C(PathTime, X) → C(PathTime, X))
    (hf : AEMeasurable f (μ : Measure C(PathTime, X)))
    (hs : ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)), range (f γ) ⊆ range γ)
    (hη : (η : Measure C(PathTime, X)) ≤
      (2 : ℝ≥0∞) • (μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)))
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ α, pathImageCount {x | (t, x) ∈ H} α ∂(η : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ α : C(PathTime, X) ∂(η : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range α ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  filter_upwards [hgeneric] with t ht
  have hclosed : IsClosed {x | (t, x) ∈ H} :=
    hH.preimage (continuous_const.prodMk continuous_id)
  have hm := hfull.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hd := hdom.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hb := hflag.comp (measurable_id.prodMk (measurable_const (a := t)))
  have hp : MeasurableSet {α : C(PathTime, X) |
      pathImageCount {x | (t, x) ∈ H} α < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} α ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) α +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) α} :=
    (measurableSet_lt hm measurable_const).inter (measurableSet_le hm (hd.add hb))
  have hselected : ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} (f γ) < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} (f γ) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (f γ) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (f γ) := by
    filter_upwards [hs, ht.2, ae_lt_top hm ht.1.ne] with γ hsub hfree hfin
    have hfree' : ¬ ∃ x ∈ range (f γ) ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
      rintro ⟨x, ⟨hx, hxf⟩, hxH⟩
      exact hfree ⟨x, ⟨hsub hx, hxf⟩, hxH⟩
    exact ⟨(pathImageCount_mono_range _ hsub).trans_lt hfin,
      pathImageCount_level_le_of_no_free_hits U Flags _ (f γ) hfree'⟩
  have hmap : ∀ᵐ α : C(PathTime, X) ∂(μ.map (f := f) (by first | exact hf | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, X)),
      pathImageCount {x | (t, x) ∈ H} α < ∞ ∧
      pathImageCount {x | (t, x) ∈ H} α ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) α +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) α := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff hf hp).mpr hselected
  refine ⟨finite_mean_subarc_intersections μ η f hf hs hη hclosed ht.1, ?_⟩
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hη).ae_le hmap] with α hα
  exact no_free_hits_of_finite_count_le U Flags _ hdisj α hα.1 hα.2

theorem IsSubarcLawReduction.generic_levels
    {μ η : ProbabilityMeasure C(PathTime, X)} (hred : IsSubarcLawReduction μ η)
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    (hgeneric : ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (t, x) ∈ H} γ ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ α, pathImageCount {x | (t, x) ∈ H} α ∂(η : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ α : C(PathTime, X) ∂(η : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range α ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  obtain ⟨f, hf, hs, hη⟩ := hred
  exact subarc_generic_levels μ η f hf hs hη hH U Flags hU hFlags hdisj hgeneric

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcMeanCircleCompatibility
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply mean-circle compatibility to the actual compact subarc law.
Both finite counts and free avoidance are inherited from the original
endpoint law through its proved measurable selection witness. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem subarc_mean_circle_compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {B U Flags S : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B) (hdust : π '' Gᶜ ⊆ B)
    (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (hS : IsOpen S)
    (harcs : ∀ C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (μ ν : ProbabilityMeasure C(PathTime, X)) (hred : IsSubarcLawReduction μ ν)
    (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, X))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, X) ∂(μ : Measure C(PathTime, X)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (Rnew : Set (X × UnitAddCircle)) (hnew : IsClosed Rnew)
    (hnewlevel : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ t, (x, t) ∈ Rnew ↔
      diskMeanCircle hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (F x) = t)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure ((Uᶜ \ Flags) ∩ S) Rnew R labels) = 0 := by
  have hUm : MeasurableSet U := by
    obtain ⟨Q, hQ, hcov⟩ := hU
    rw [← hcov]
    exact MeasurableSet.iUnion (fun n => (hQ n).measurableSet)
  apply mean_circle_compatibility_of_generic_levels hsch hsep hLusin π hπ hsurj hfiber
    hG hB hTD hdust (hUm.compl.diff hFlags.measurableSet) hS harcs
    A K hK hKS η F f hf hmap h0 h1 hF hinj R hR hlength _ Rnew hnew hnewlevel n labels
  intro i
  have hgood := hred.generic_levels ((hR i).preimage continuous_swap)
    U Flags hU hFlags hdisj (hgeneric i)
  filter_upwards [hgood] with t ht
  refine ⟨by simpa only [hη, mem_preimage, Prod.swap_prod_mk] using ht.1, ?_⟩
  have hm := ht.2
  rw [← hη, ProbabilityMeasure.toMeasure_map] at hm
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanPeriodCompatibility
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked mean-period graph satisfies ordered compatibility.
The boundary of the mask lies in the physical domain, so restricting to
its open interior loses no free incidences. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_rbedb44_8 : BorelSpace Sphere := ⟨rfl⟩
theorem mean_period_graph_compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Y → Sphere) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G : Set Y} (hG : IsOpen G) {Dust U Flags S M : Set Sphere}
    (hDust : IsCompact Dust) (hTD : IsTotallyDisconnected Dust) (hdust : π '' Gᶜ ⊆ Dust)
    (hU : IsSigmaCompact U) (hdense : Dense U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (b : Sphere) (hb : b ∈ Flags)
    (hboundary : M \ interior M ⊆ U) (hMS : M \ {b} ⊆ S)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (μ ν : ProbabilityMeasure C(PathTime, Sphere)) (hred : IsSubarcLawReduction μ ν)
    (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ (interior M \ {b})))
    (hinj : InjOn F (interior M \ {b}))
    (hmiss : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ᵐ γ : K ∂((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K),
      F x ∉ range γ.val)
    {I : Type*} (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i))
    (hVS : ∀ i, closure (V i) ⊆ S) (hbV : ∀ i, b ∉ V i)
    (hcover : M \ {b} ⊆ ⋃ i, V i)
    (a B : I → ℝ) (u : I → Sphere → ℝ)
    (hbound : ∀ i x, x ∈ U → |u i x| ≤ B i)
    (hlog : ∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i)))
    (htrans : ∀ i j x, x ∈ V i → x ∈ V j →
      ∃ k : ℤ, u j =ᶠ[𝓝[U] x] fun y => u i y + k)
    (error : Sphere → ℝ) (herror : ∀ x ∈ Uᶜ \ Flags, Tendsto error (𝓝[U] x) (𝓝 0))
    (hu : ∀ i x, x ∈ V i → u i x =
      meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
        (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x))) + error x)
    (hclosed : IsClosed (periodBandGraph U M b V u))
    (R : ℕ → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Y) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Uᶜ \ Flags) (periodBandGraph U M b V u) R labels) = 0 := by
  have hbfree : b ∉ Uᶜ \ Flags := fun hx => hx.2 hb
  have hWS : interior M \ {b} ⊆ S := fun x hx => hMS ⟨interior_subset hx.1, hx.2⟩
  have hsupport : ∀ x ∈ Uᶜ \ Flags, ∀ t, (x, t) ∈ periodBandGraph U M b V u →
      x ∈ interior M \ {b} := by
    intro x hx t ht
    refine ⟨?_, fun he => hx.2 (he ▸ hb)⟩
    by_contra hn
    exact hx.1 (hboundary ⟨ht.1, hn⟩)
  rw [← freeComponentFailure_inter_eq_of_support (Uᶜ \ Flags) (interior M \ {b})
    (periodBandGraph U M b V u) R labels hsupport]
  apply subarc_mean_circle_compatibility hsch hsep hLusin π hπ hsurj hfiber
    hG hDust hTD hdust hU hFlags hdisj (isOpen_interior.sdiff isClosed_singleton)
    harcs A K hK hKS η F f hf hmap μ ν hred hη
    (fun x hx => h0 x (hWS hx)) (fun x hx => h1 x (hWS hx)) hF hinj
    R hR hlength hgeneric (periodBandGraph U M b V u) hclosed _ n labels
  intro x hx t
  rw [period_graph_mean_free_value hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F U M S
    (Uᶜ \ Flags) hdense b hbfree h0 h1 hmiss V hV hVS hbV hcover a B u
    hbound hlog htrans error herror hu x hx.1 t]
  exact and_iff_right (interior_subset hx.2.1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanPeriodConsequences
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed smooth mean coordinate has the actual point-hit
budget and satisfies compatibility with every finite prior level union. -/

open Set Function Filter MeasureTheory Classical
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_17
theorem SmoothMeanPeriodData.compatibility
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (π : Sphere → Sphere) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    {G U Dust Flags S M : Set Sphere} (hG : IsOpen G)
    (hDust : IsCompact Dust) (hTD : IsTotallyDisconnected Dust) (hdust : π '' Gᶜ ⊆ Dust)
    (hU : IsSigmaCompact U) (hdense : Dense U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags) (b : Sphere) (hb : b ∈ Flags) (hbS : b ∉ S)
    (hboundary : M \ interior M ⊆ U) (hMS : M \ {b} ⊆ S)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (μ ν : ProbabilityMeasure C(PathTime, Sphere)) (hred : IsSubarcLawReduction μ ν)
    (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ (Uᶜ \ Flags) ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π)
    (R : ℕ → Set (Sphere × UnitAddCircle)) (hR : ∀ i, IsClosed (R i))
    (hlength : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (μH[1] : Measure Sphere) (G ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hgeneric : ∀ i, ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, t) ∈ R i} γ
        ∂(μ : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (Uᶜ \ Flags), (x, t) ∈ R i)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (Uᶜ \ Flags) (periodBandGraph U M b Q.patch Q.branch) R labels) = 0 := by
  have hWS : interior M \ {b} ⊆ S := fun x hx => hMS ⟨interior_subset hx.1, hx.2⟩
  exact mean_period_graph_compatibility hsch hsep hLusin π hπ hsurj hfiber hG
    hDust hTD hdust hU hdense hFlags hdisj b hb hboundary hMS harcs A K hK hKS η F f hf hmap
    μ ν hred hη h0 h1 (fun γ => (hF γ).mono (union_subset_union Subset.rfl hWS))
    (hinj.mono hWS)
    (fun x hx => mapped_arc_point_avoidance A K η F f hf hmap x
      (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hx.2)))
      (hmiss x hx))
    Q.patch Q.patch_open Q.patch_closure
    (fun i hi => hbS (Q.patch_closure i (subset_closure hi))) (hMS.trans Q.cover)
    Q.angle Q.bound Q.branch (fun i x _ => Q.bounded i x) Q.log_continuous Q.transition
    Q.error (fun x hx => (Q.error_vanishes x hx.1).mono_left nhdsWithin_le_nhds)
    Q.branch_value Q.closed R hR hlength hgeneric n labels

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RestrictedCoordinateMarks
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable selected family uses only countably many nonzero bands.
Restricting to these marks preserves the actual graph, physical function
and masks; every discarded marked fiber is already a singleton. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.countable_band_support
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) :
    {s | C.upper s - C.lower s ≠ 0}.Countable :=
  CircleDomainRigidity.countable_band_support C.width_summable

 theorem exists_common_countable_coordinate_marks
    {I S : Type*} [Countable I] {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : I → MaskedCoordinateData G U π σ) (B : Set S) (hB : B.Countable) :
    ∃ A : Set S, A.Countable ∧ B ⊆ A ∧
      (∀ i, (C i).singular ∈ A) ∧
      ∀ i s, (C i).upper s - (C i).lower s ≠ 0 → s ∈ A := by
  let A := B ∪ range (fun i => (C i).singular) ∪ ⋃ i, {s | (C i).upper s - (C i).lower s ≠ 0}
  refine ⟨A, (hB.union (countable_range _)).union
    (countable_iUnion fun i => (C i).countable_band_support), ?_, ?_, ?_⟩
  · intro s hs
    exact Or.inl (Or.inl hs)
  · intro i
    exact Or.inl (Or.inr (mem_range_self i))
  · intro i s hs
    exact Or.inr (mem_iUnion.mpr ⟨i, hs⟩)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_MaskedLevelData
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual marked band widths supply the level weights for the next
endpoint-law construction. This uses the full dust as a temporary label
set; the common countable mark restriction is performed after selection. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B : Set Sphere} {π : Sphere → Sphere}
  (C : MaskedCoordinateData G U π (fun x : B => x.val))

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
theorem dustWeight_square_sum : (∑' x, C.dustWeight x ^ 2) < ∞ := by
  classical
  have he : (∑' x, C.dustWeight x ^ 2) =
      ∑' s : B, ENNReal.ofReal ((C.upper s - C.lower s) ^ 2) := by
    have hsupp : support (fun x => C.dustWeight x ^ 2) ⊆ B := by
      intro x hx
      by_contra hn
      exact hx (by simp only [dustWeight, dite_eq_right hn, zero_pow (by decide : 2 ≠ 0)])
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    apply tsum_congr
    intro s
    simp only [dustWeight, dite_eq_left s.property,
      ENNReal.ofReal_pow (C.width_nonneg s)]
  rw [he, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) C.width_summable]
  exact ENNReal.ofReal_lt_top

end FiniteTransfer.MaskedCoordinateData

variable [MeasurableSpace C(PathTime, Sphere)]

namespace maskedLevelData
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
    (fun x : d.dust => x.val))

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_21
theorem exists_countable_flags (B₀ : Set Sphere) (hB₀ : B₀.Countable)
    (hB₀B : B₀ ⊆ d.dust) :
    ∃ flags : Set Sphere, flags.Countable ∧ B₀ ⊆ flags ∧ flags ⊆ d.dust ∧
      (∀ i, ((C i).singular : Sphere) ∈ flags) ∧
      ∀ i, support ((maskedLevelData d π C).levelWeights i) ⊆ flags := by
  obtain ⟨A, hA, hBA, hs, hw⟩ := exists_common_countable_coordinate_marks C
    (Subtype.val ⁻¹' B₀) (hB₀.preimage Subtype.val_injective)
  refine ⟨Subtype.val '' A, hA.image _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hB₀B hx⟩, hBA hx, rfl⟩
  · rintro x ⟨s, _, rfl⟩
    exact s.property
  · intro i
    exact ⟨(C i).singular, hs i, rfl⟩
  · intro i x hx
    change (C i).dustWeight x ≠ 0 at hx
    by_cases hxB : x ∈ d.dust
    · refine ⟨⟨x, hxB⟩, hw i ⟨x, hxB⟩ ?_, rfl⟩
      intro he
      exact hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_left hxB, he,
        ENNReal.ofReal_zero])
    · exact (hx (by simp only [MaskedCoordinateData.dustWeight, dite_eq_right hxB])).elim

end maskedLevelData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PresentedPriorLevels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual countable real/mean presentations give generic prior-level
estimates for the path law. Closedness, square-summable weights, and free
weights are obtained from the stored coordinates and common marks. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance localInst_rbedb44_9 : BorelSpace Sphere := ⟨rfl⟩
theorem presented_prior_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hdust : d.dust = d.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (C : ℕ → MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch d π (C i))
    (hlevel : ∀ i, d.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, d.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (d.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hvisits : ∀ i, countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ i x, x ∈ support (d.levelWeights i) → ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω) :
    ∀ i, ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ (C i).graph} γ
        ∂(codePathLaw d P : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (d.quotientDomainᶜ \ Flags), (x, θ) ∈ (C i).graph := by
  have hH (i : ℕ) : IsClosed (d.levels i) := by
    rw [hlevel i]
    exact (C i).graph_closed.preimage continuous_swap
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  intro i
  have hm : (support (d.levelWeights i)).Countable := hFlags.mono (hmarked i)
  have hw : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞ := by
    apply (countingSquareNorm_comp_injective (d.levelWeights i)
      (fun x : support (d.levelWeights i) => x.val) Subtype.val_injective).trans_lt
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    rw [hweights i]
    exact (C i).dustWeight_square_sum.ne
  have hfree (x : Sphere) (hx : x ∈ d.quotientDomainᶜ \ Flags) : d.levelWeights i x = 0 := by
    by_contra hn
    exact hx.2 (hmarked i hn)
  have hg := (presentation i).generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hw (hvisits i) hfree (hcover i) hdeletions hH hP hunique ω hτ hsep
    (C i) (hlevel i) (hweights i) (hsingular i)
  have hdj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr (fun x hx hxf => hFlagsB hxf hx)
  have hh := map_generic_levels P (codePath d) (measurable_codePath d) (hH i)
    d.quotientDomain Flags hσU hFlags hdj hg
  simpa only [codePathLaw, hlevel i, mem_preimage, Prod.swap_prod_mk] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RebasedLevelPresentations
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a target or prior law changes the code space, but preserves the
actual selected coordinates and their real/mean presentations. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

namespace FiniteTransfer.MaskedCoordinateData
variable {G U B G' U' B' : Set Sphere} {π : Sphere → Sphere}

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_25
theorem dustWeight_rebaseDust (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hG : G' = G) (hU : U' = U) (hB : B' = B) :
    (C.rebaseDust hG hU hB).dustWeight = C.dustWeight := by
  subst G'; subst U'; subst B'
  rfl

end FiniteTransfer.MaskedCoordinateData

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RecursiveLawLevelEstimates
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursively selected positive law supplies the visit and deletion
estimates required by all earlier real and mean levels. No generic-level
assumption remains in this application. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_26
theorem RecursiveCodeLaw.generic_prior_levels
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω) :
    ∀ i, ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ (C i).graph} γ
        ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (base.quotientDomainᶜ \ Flags), (x, θ) ∈ (C i).graph := by
  let D (i : ℕ) := (C i).rebaseDust L.physical_eq L.quotient_eq L.dust_eq
  have hpres (i : ℕ) : SelectedLevelPresentation hsch L.data π (D i) :=
    (presentation i).rebase L.physical_eq L.quotient_eq L.dust_eq
  have hlev (i : ℕ) : L.data.levels i = Prod.swap ⁻¹' (D i).graph := by
    rw [L.levels_eq, hlevel i]
    exact congrArg (fun T => Prod.swap ⁻¹' T)
      ((C i).graph_rebaseDust L.physical_eq L.quotient_eq L.dust_eq).symm
  have hwgt (i : ℕ) : L.data.levelWeights i = (D i).dustWeight := by
    rw [L.weights_eq, hweights i]
    exact ((C i).dustWeight_rebaseDust L.physical_eq L.quotient_eq L.dust_eq).symm
  have hm (i : ℕ) : support (L.data.levelWeights i) ⊆ Flags := by
    rw [L.weights_eq]
    exact hmarked i
  have hs (i : ℕ) : ((D i).singular : Sphere) ∈ Flags := by
    rw [(C i).singular_rebaseDust]
    exact hsingular i
  have hv (i : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights i) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ := by
    rw [L.weights_eq]
    exact L.flag_visit_norm_finite i (hmarked i)
  have hc : ∀ i x, x ∈ support (L.data.levelWeights i) →
      ∀ᶠ n in atTop, x ∈ L.data.flagDeletions n := by
    intro i x hx
    rw [L.weights_eq] at hx
    simpa only [L.flag_deletions_eq] using L.presentation.flag_cover x (hmarked i hx)
  have hd : ∀ n, (L.data.flagDeletions n : Set Sphere) ⊆ Flags := by
    intro n
    simpa only [L.flag_deletions_eq] using L.presentation.flag_subset n
  have hg := presented_prior_generic_levels rank hrank hcoarea hsard hsch hsep L.data
    (by simpa only [L.physical_eq] using hG)
    (by simpa only [L.quotient_eq] using hU)
    (by simpa only [L.quotient_eq] using hdense)
    (by simpa only [L.dust_eq, L.quotient_eq] using hdust)
    π hπ hclosed hsurj (by simpa only [L.physical_eq] using hr) L.domain_agrees
    (by simpa only [L.quotient_eq] using hTD)
    (by simpa only [L.physical_eq, L.quotient_eq] using hbad)
    Flags hFlags (by simpa only [L.quotient_eq] using hFlagsB)
    L.law L.density L.density_measurable L.occupation_eq L.density_energy_finite D hpres hlev hwgt
    hm hs hv hc hd (by simpa only [L.levels_eq, L.quotient_eq] using hP)
    (by simpa only [L.levels_eq, L.quotient_eq] using hunique)
    ω L.tuple_absolutelyContinuous
  simpa only [D, MaskedCoordinateData.graph_rebaseDust, L.quotient_eq] using hg

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_SelectableMaskedCoordinate
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected coordinate retains the precise level and flag data needed
for a later endpoint-law construction. Weighted coarea is proved for the
actual physical mean before placing it in this interface. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem SmoothMeanPeriodData.domain_fiber_subsingleton
    (hsch : PlanarSchoenflies) (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    {G U S M : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    (Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π)
    (x : Sphere) (hx : x ∈ U) :
    {t : UnitAddCircle | (x, t) ∈ periodBandGraph U M b Q.patch Q.branch}.Subsingleton := by
  intro a ha b hb
  exact ((Q.domain_value x hx a).mp ha).2.symm.trans ((Q.domain_value x hx b).mp hb).2

namespace SelectableMaskedCoordinate

 local instance localInst_rbedb44_10 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_of_mean
    (hcoarea : WeightedPlanarScalarCoarea) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → π (z : Sphere) ∈ d.quotientDomain)
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S M : Set Sphere) (hS : IsOpen S) (b : Sphere) (hbU : b ∉ d.quotientDomain)
    (hMS : M \ {b} ⊆ S)
    (Q : SmoothMeanPeriodData hsch K hKS η F d.physicalDomain d.quotientDomain S M b π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π (fun x : d.dust => x.val))
    (hgraph : C.graph = periodBandGraph d.quotientDomain M b Q.patch Q.branch)
    (flags : Set Sphere) (hflags : flags.Countable) (hflagsB : flags ⊆ d.dust) :
    ∃ c : SelectableMaskedCoordinate d π, c.coordinate = C ∧ flags ⊆ c.flags := by
  obtain ⟨Z, hZ, hfZ, hZB, hsing, hweights⟩ :=
    maskedLevelData.exists_countable_flags (fun _ => C) flags hflags hflagsB
  refine ⟨{
    coordinate := C
    flags := Z
    flags_countable := hZ
    flags_dust := hZB
    weight_support := hweights 0
    singular_marked := hsing 0
    domain_unique := ?_
    weighted := ?_ }, rfl, hfZ⟩
  · intro x hx
    rw [hgraph]
    exact Q.domain_fiber_subsingleton hsch K hKS η F x hx
  · intro g hg henergy
    rw [hgraph]
    exact Q.ae_finite_weighted_levels hcoarea hsch K hKS η F hG hS hbU hMS hπ hPU
      g hg henergy

end SelectableMaskedCoordinate

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_OrderedMaskedSelection
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected mixed family retains the complete seed before the new
coordinates. Empty selection steps use the seed zero coordinate. The
resulting order has type omega plus omega, not a rearranged natural order. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem freeComponentFailure_mono_free {X T I J : Type*} [TopologicalSpace X]
    {F K : Set X} (hFK : F ⊆ K) (N : Set (X × T)) (R : I → Set (X × T)) (labels : J → I) :
    freeComponentFailure F N R labels ⊆ freeComponentFailure K N R labels := by
  rintro _ ⟨⟨x, t, θ⟩, h, rfl⟩
  exact ⟨(x, t, θ), ⟨hFK h.1, h.2⟩, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RecursiveMeanCompatibility
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursive positive law gives compatibility for the next smoothed
mean. Generic prior intersections follow from its retained real and mean
data and candidate budgets. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_27
theorem RecursiveCodeLaw.mean_coordinate_compatible
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (Flags' : Set Sphere) (hFlags' : Flags'.Countable)
    (hFlagsB' : Flags' ⊆ base.quotientDomainᶜ) (hFlagsMono : Flags ⊆ Flags')
    (S M : Set Sphere) (b : Sphere) (hb : b ∈ Flags') (hbS : b ∉ S)
    (hboundary : M \ interior M ⊆ base.quotientDomain) (hMS : M \ {b} ⊆ S)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (ν : ProbabilityMeasure C(PathTime, Sphere))
    (hred : IsSubarcLawReduction (codePathLaw L.data L.law) ν)
    (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ (base.quotientDomainᶜ \ Flags') ∩ S,
      ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F
      base.physicalDomain base.quotientDomain S M b π)
    (n : ℕ) (labels : Fin n → ℕ) :
    (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
      (freeComponentFailure (base.quotientDomainᶜ \ Flags')
        (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph labels) = 0 := by
  have hg := L.generic_prior_levels rank hrank hcoarea hsard hsch hsep base
    hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB C presentation
    hlevel hweights hmarked hsingular hP hunique ω
  have hgeneric (i : ℕ) : ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ γ, pathImageCount {x | (x, θ) ∈ previous.graph i} γ
        ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere))) < ∞ ∧
      ∀ᵐ γ : C(PathTime, Sphere) ∂(codePathLaw L.data L.law : Measure C(PathTime, Sphere)),
        ¬ ∃ x ∈ range γ ∩ (base.quotientDomainᶜ \ Flags'), (x, θ) ∈ previous.graph i := by
    rw [hprevious i]
    filter_upwards [hg i] with θ hθ
    refine ⟨hθ.1, ?_⟩
    filter_upwards [hθ.2] with γ hγ
    rintro ⟨x, ⟨hxγ, hxB, hxF⟩, hxi⟩
    exact hγ ⟨x, ⟨hxγ, hxB, fun hx => hxF (hFlagsMono hx)⟩, hxi⟩
  have hσU : IsSigmaCompact base.quotientDomain := by
    let : LocallyCompactSpace base.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  apply Q.compatibility hsch hsep hLusin π hπ hsurj hfiber hG
    (show IsCompact base.dust from by rw [hdust]; exact hU.isClosed_compl.isCompact)
    (by rwa [hdust])
    (by rintro _ ⟨x, hx, rfl⟩; exact hdust.symm ▸ hbad x hx)
    hσU hdense hFlags'
    (disjoint_left.mpr (fun x hx hxF => hFlagsB' hxF hx)) b hb hbS hboundary hMS harcs
    A K hK hKS η F f hf hmap (codePathLaw L.data L.law) ν hred hη h0 h1 hF hinj hmiss
    previous.graph previous.closed previous.length hgeneric n labels

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SubarcPointAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point avoidance outside the original law's positive-hit set survives
the actual subarc selector and compact conditioning. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem IsSubarcLawReduction.avoids_point
    {μ ν : ProbabilityMeasure C(PathTime, Sphere)} (hred : IsSubarcLawReduction μ ν)
    {x : Sphere} (hx : pathHitProbability μ x = 0) :
    ∀ᵐ γ : C(PathTime, Sphere) ∂(ν : Measure C(PathTime, Sphere)), x ∉ range γ := by
  obtain ⟨f, hf, hs, hν⟩ := hred
  have hμ : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)), x ∉ range γ := by
    apply ae_iff.mpr
    simpa only [not_not, mem_range, pathHitProbability] using hx
  have hsel : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ : Measure C(PathTime, Sphere)),
      x ∉ range (f γ) := by
    filter_upwards [hμ, hs] with γ hγ hsub
    exact fun hx => hγ (hsub hx)
  have hmap : ∀ᵐ γ : C(PathTime, Sphere) ∂(μ.map (f := f) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : Measure C(PathTime, Sphere)),
      x ∉ range γ := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff hf ?_).mpr hsel
    exact (isClosed_paths_hitting x).isOpen_compl.measurableSet
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le hmap

 theorem RecursiveCodeLaw.subarc_avoids_unmarked_point
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞}
    (L : RecursiveCodeLaw base π Flags ω)
    (T : Set Sphere)
    (hT : {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} ⊆ T)
    {ν : ProbabilityMeasure C(PathTime, Sphere)}
    (hred : IsSubarcLawReduction (codePathLaw L.data L.law) ν)
    {A : Set C(PathTime, Sphere)} (η : ProbabilityMeasure A) (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    {x : Sphere} (hx : x ∈ base.dust \ T) :
    ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val := by
  have hz : pathHitProbability (codePathLaw L.data L.law) x = 0 := by
    rw [pathHitProbability_codePathLaw]
    by_contra hn
    exact hx.2 (hT ⟨L.dust_eq.symm ▸ hx.1, pos_iff_ne_zero.mpr hn⟩)
  have hν := hred.avoids_point hz
  rw [← hη, ProbabilityMeasure.toMeasure_map] at hν
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hν

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.extendedHitFlags_countable
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω)
    (hFlags : Flags.Countable) : L.extendedHitFlags.Countable :=
  hFlags.union L.countable_dust_hits

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.extendedHitFlags_subset
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω)
    (hFlags : Flags ⊆ base.dust) : L.extendedHitFlags ⊆ base.dust := by
  intro x hx
  rcases hx with hx | hx
  · exact hFlags hx
  · exact L.dust_eq ▸ hx.1

 omit [BorelSpace C(PathTime, Sphere)] in
 theorem RecursiveCodeLaw.target_mem_extendedHitFlags
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} (L : RecursiveCodeLaw base π Flags ω) :
    L.data.target ∈ L.extendedHitFlags := by
  right
  refine ⟨L.dust_eq.symm ▸ L.target_dust, ?_⟩
  have heq : {Γ : BasePathCode L.data | L.data.target ∈ range Γ.val.1} = univ := by
    apply eq_univ_of_forall
    intro Γ
    exact ⟨⊤, Γ.property.2.1.2.1⟩
  change 0 < (L.law : Measure (BasePathCode L.data)) _
  rw [heq, measure_univ]
  norm_num

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SelectableMeanLaw
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The recursive positive-law alternative constructs a selectable mean
coordinate with its concrete presentation. Finite compatibility is derived
from the preceding law estimates, while preserving the coordinate’s
Stokes budget and exclusion. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_28
theorem RecursiveCodeLaw.selectable_mean_coordinate
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (Flags' : Set Sphere) (hFlags' : Flags'.Countable)
    (hFlagsB' : Flags' ⊆ base.quotientDomainᶜ) (hFlagsMono : Flags ⊆ Flags')
    (S M : Set Sphere) (b : Sphere) (hb : b ∈ Flags') (hbS : b ∉ S)
    (hboundary : M \ interior M ⊆ base.quotientDomain) (hMS : M \ {b} ⊆ S)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ)) (hK : IsCompact K)
    (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (ν : ProbabilityMeasure C(PathTime, Sphere))
    (hred : IsSubarcLawReduction (codePathLaw L.data L.law) ν)
    (hη : η.map (f := Subtype.val) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = ν)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hFlagsHits : {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} ⊆ Flags')
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F
      base.physicalDomain base.quotientDomain S M b π)
    (hweighted : WeightedPlanarScalarCoarea)
    (hebase : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hstrict : ∀ x ∈ M \ base.quotientDomain, ‖F x‖ < 1)
    (hS : IsOpen S) (hM : IsClosed M) (hinftyM : π OnePoint.infty ∉ M) (hbM : b ∈ M)
    (N : MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (hN : N.graph = periodBandGraph base.quotientDomain M b Q.patch Q.branch)
    (hNb : (N.singular : Sphere) = b)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags')
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.coordinate = N ∧
      c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) := by
  have hmiss : ∀ x ∈ (base.quotientDomainᶜ \ Flags') ∩ S,
      ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val := by
    intro x hx
    exact L.subarc_avoids_unmarked_point Flags' hFlagsHits hred η hη
      ⟨hdust.symm ▸ hx.1.1, hx.1.2⟩
  have hPU (z : ℂ) (hz : (z : Sphere) ∈ base.physicalDomain) :
      π (z : Sphere) ∈ base.quotientDomain := by
    rw [← hebase ⟨z, hz⟩]
    exact (base.domainEquiv ⟨z, hz⟩).property
  obtain ⟨c, hc, hmark⟩ := SelectableMaskedCoordinate.exists_of_mean hweighted hsch base hG
    π hπ hPU K hKS (η.map (f := f) (hf.aemeasurable)) F S M hS b (hFlagsB' hb) hMS Q N hN
    Flags' hFlags' (fun x hx => hdust.symm ▸ hFlagsB' hx)
  have hcomp (n : ℕ) (ls : Fin n → ℕ) :
      (volume.prod (Measure.pi (fun _ : Fin n => (volume : Measure UnitAddCircle))))
        (freeComponentFailure (base.quotientDomainᶜ \ Flags')
          (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph ls) = 0 :=
    L.mean_coordinate_compatible rank hrank hcoarea hsard hsch hsep base
      hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB C presentation
      hlevel hweights hmarked hsingular hP hunique ω hLusin hfiber harcs previous hprevious
      Flags' hFlags' hFlagsB' hFlagsMono S M b hb hbS hboundary hMS A K hK hKS η F f hf
      hmap ν hred hη h0 h1 hF hinj hmiss Q n ls
  refine ⟨c, hc, ⟨?_, ?_⟩, ?_⟩
  · exact fun a ha => (hflags a ha).trans hmark
  · intro n q hq
    rw [hc, hN]
    have hz := hcomp n (label ∘ q)
    rw [UngatedRealTest.freeComponentFailure_congr_selected (base.quotientDomainᶜ \ Flags')
      (periodBandGraph base.quotientDomain M b Q.patch Q.branch) previous.graph
      (fun i : Fin n => (q i).coordinate.graph) (label ∘ q) id
      (fun i => (hgraphs (q i) (hq i)).symm)] at hz
    apply measure_mono_null (freeComponentFailure_mono_free ?_ _ _ id) hz
    intro x hx
    exact ⟨hdust ▸ hx.1, fun hm => hx.2 (hmark hm)⟩
  · refine ⟨{
      arcs := A
      diskArcs := K
      compact_diskArcs := hK
      terminal_diskArcs := hKS
      law := η
      map := F
      arcMap := f
      measurable_arcMap := hf
      arcMap_eq := hmap
      neighborhood := S
      mask := M
      open_neighborhood := hS
      closed_mask := hM
      excludes_infty := hinftyM
      boundary_domain := hboundary
      singular := b
      singular_eq := by rw [hc]; exact hNb
      singular_dust := hdust.symm ▸ hFlagsB' hb
      singular_mask := hbM
      singular_outside := hbS
      punctured_mask := hMS
      nonzero := h0
      unit_bound := h1
      strict_bound := hstrict
      injective_arcs := hF
      mean := Q
      graph_eq := by rw [hc]; exact hN }⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanExclusionRadius
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed mean exclusion remains valid for every smaller target-radius
budget. This permits an open radius interval in the common selection space. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem boundary_in_mask (z : ℂ) (hz : z ∈ frontier (jordanInterior W.disk)) :
    π (z : Sphere) ∈ N.mask := by
  have hx : Complex.equivRealProdCLM z ∈ realChartDomain (closedTerminalCap W.disk) := by
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ closedTerminalCap W.disk
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ (frontier_subset_closure hz)
  have hm := interior_subset (W.mask hx)
  change π ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ N.mask at hm
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm

 theorem boundary_norm_lt {B : ℝ}
    (hB : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∉ N.mask) :
    ∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B := by
  intro z hz
  by_contra hn
  exact hB z (not_lt.mp hn) (W.boundary_in_mask z hz)

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectableRecursiveMean
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed recursive mean is compatible with the actual preceding
selected presentations. Its physical coordinate and open exclusion are retained. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_29
theorem RecursiveMeanOutput.selectable
    {O : Type*} [LinearOrder O] (rank : ℕ → O) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    (Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε)
    {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c₀ : ℂ} {r₀ : ℝ≥0} {R₀ δ : ℝ}
    (R : RecursiveMeanOutput hsch Q F₀ hF₀ c₀ r₀ R₀ δ)
    (hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (hweighted : WeightedPlanarScalarCoarea)
    (hebase : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ L.extendedHitFlags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c)) :
    ∃ c : SelectableMaskedCoordinate base π, c.coordinate = R.coordinate ∧
      c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      c.coordinate.sourceStokesBudget R₀ < δ ∧
      Nonempty (MeanExclusionWitness c.coordinate F₀ hF₀ c₀ r₀ R₀) := by
  have hExt : L.extendedHitFlags ⊆ base.quotientDomainᶜ := by
    rw [← hdust]
    exact L.extendedHitFlags_subset (fun x hx => hdust.symm ▸ hFlagsB hx)
  have hboundary : R.mask \ interior R.mask ⊆ base.quotientDomain := by
    intro x hx
    apply R.frontier
    rw [_root_.frontier, R.closed.closure_eq]
    exact hx
  have hMS : R.mask \ {L.data.target} ⊆ R.centered.punctured :=
    fun _ hx => ⟨R.inner hx.1, hx.2⟩
  obtain ⟨c, hc, hcomp, hpres⟩ := L.selectable_mean_coordinate rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad
    Flags hFlags hFlagsB C presentation hlevel hweights hmarked hsingular hP hunique ω
    hLusin hfiber harcs previous hprevious
    L.extendedHitFlags (L.extendedHitFlags_countable hFlags) hExt (fun _ hx => Or.inl hx)
    R.centered.punctured R.mask L.data.target L.target_mem_extendedHitFlags
    (fun h => h.2 rfl) hboundary hMS Q.arcs R.centered.diskArcs R.centered.compact
    R.centered.terminal Q.law R.centered.map R.centered.arcMap
    R.centered.continuous_arcMap.measurable R.centered.arcMap_eq
    (Q.law.map (f := Subtype.val) measurable_subtype_coe.aemeasurable) Q.reduction rfl (R.centered.nonzero hbJ)
    (R.centered.norm_le hbJ) (R.centered.injective_arcs hbJ Q.terminal)
    (R.centered.injective_punctured hbJ) (fun _ hx => Or.inr hx)
    R.mean hweighted hebase (fun x hx => R.centered.norm_lt hbJ x (R.inner hx.1))
    R.centered.punctured_open R.closed R.infty_not_mem R.target_mem
    R.coordinate R.graph R.singular_eq Candidates label hflags hgraphs

  refine ⟨c, hc, hcomp, hpres, ?_, ?_⟩
  · rw [hc]
    exact R.budget
  · rw [hc]
    exact ⟨R.exclusion⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SizedMeanExclusion
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Record the exterior model radius in the same second countable test
space. An open radius interval retains the quantitative Stokes exclusion
under subsequent common-model selection. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MeanExclusionWitness
variable {T : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : T → Sphere}
    {N : MaskedCoordinateData G U π σ} {F₀ : ℂ → ℂ}
    {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G)} {c : ℂ} {r : ℝ≥0} {R : ℝ}
    (W : MeanExclusionWitness N F₀ hF₀ c r R)

 theorem mem_sizedNeighborhood {B ρ : ℝ} (hB : B < ρ) (hρ : 5 * ρ < R) :
    ((finiteSourceMap F₀ hF₀, c, r), ρ) ∈ W.sizedNeighborhood B :=
  ⟨W.member, hB, by linarith⟩

end MeanExclusionWitness
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_AnchoredMeanSourceBound
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained inner mean circuit stays outside the fixed endpoint
anchor. Its physical radius is therefore bounded before the final model
radius is chosen. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem RecursiveMeanOutput.boundary_norm_lt_of_anchor
    {hsch : PlanarSchoenflies} {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {Flags : Set Sphere} {ω : TupleType → ℝ≥0∞} {L : RecursiveCodeLaw base π Flags ω}
    {J : ℂ ≃ₜ ℂ} {ε : ℝ≥0∞}
    {Q : CompactRecursiveReduction L (((↑) : ℂ → Sphere) '' jordanInterior J) ε}
    {F₀ : ℂ → ℂ} {hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' base.physicalDomain)}
    {c : ℂ} {r : NNReal} {R δ : ℝ} (N : RecursiveMeanOutput hsch Q F₀ hF₀ c r R δ)
    (hanchor : Disjoint base.anchor (((↑) : ℂ → Sphere) '' jordanInterior J))
    {B : ℝ} (hB : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    ∀ z ∈ _root_.frontier (jordanInterior N.exclusion.disk), ‖z‖ < B := by
  apply N.exclusion.boundary_norm_lt
  intro z hz hm
  have hmask : π (z : Sphere) ∈ N.mask := by
    rwa [N.mask_eq] at hm
  exact disjoint_left.mp hanchor (hB z hz) (N.inner hmask)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectableProtrusionMean
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual gated law at a protrusion gives a compatible selectable
mean test and an open exclusion containing the original sized map--disk
pair. The circuit bound comes from the fixed exterior anchor. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 local instance instBorelSpaceSphere_30_rbedb44_1 : BorelSpace Sphere := ⟨rfl⟩
theorem RecursiveCodeLaw.exists_selectable_protrusion_mean_oai
    {I : Type*} [LinearOrder I] (rank : ℕ → I) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (base : PathCodeData Sphere Sphere)
    (hG : IsOpen base.physicalDomain) (hU : IsOpen base.quotientDomain)
    (hdense : Dense base.quotientDomain) (hdust : base.dust = base.quotientDomainᶜ)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ base.physicalDomainᶜ ∧ y ∈ connectedComponentIn base.physicalDomainᶜ x))
    (he : ∀ x : base.physicalDomain, (base.domainEquiv x).val = π x.val)
    (hTD : IsTotallyDisconnected base.quotientDomainᶜ)
    (hbad : ∀ p ∈ base.physicalDomainᶜ, π p ∈ base.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ base.quotientDomainᶜ)
    (C : ℕ → MaskedCoordinateData base.physicalDomain base.quotientDomain π
      (fun x : base.dust => x.val))
    (presentation : ∀ i, SelectedLevelPresentation hsch base π (C i))
    (hlevel : ∀ i, base.levels i = Prod.swap ⁻¹' (C i).graph)
    (hweights : ∀ i, base.levelWeights i = (C i).dustWeight)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ Flags)
    (hsingular : ∀ i, ((C i).singular : Sphere) ∈ Flags)
    (hP : RankedLevelNullCompatibility rank base.levels (base.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ base.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (L : RecursiveCodeLaw base π Flags ω)
    (hLusin : FiniteTorusAnalyticMeasurability)
    (hfiber : ∀ x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀ D : Set Sphere, IsCompact D → LocallyConnectedSpace D →
      HasSimpleArcsInConnectedOpens D)
    (previous : PriorLevelFamily base.physicalDomain π)
    (hprevious : ∀ i, previous.graph i = (C i).graph)
    (hweighted : WeightedPlanarScalarCoarea) (hcollar : SmoothRegularJordanCollars)
    (hselect : BorelPathRelationSelection)
    (Candidates : Set (SelectableMaskedCoordinate base π))
    (label : SelectableMaskedCoordinate base π → ℕ)
    (hflags : ∀ c ∈ Candidates, c.flags ⊆ Flags)
    (hgraphs : ∀ c ∈ Candidates, c.coordinate.graph = previous.graph (label c))
    {S : Type*} {σ : S → Sphere} {d : CountableRealCoordinates base.physicalDomain π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    {A : AssignedRealModelLimit M} {q : Sphere} (E : RealTargetEnd A q)
    (T : LocalEndTestGeometry E) (hq : q ∈ base.physicalDomainᶜ)
    (s : S) (hqs : π q = σ s) (htarget : L.data.target = σ s)
    (hp : L.data.target ≠ π OnePoint.infty)
    (hseparated : Disjoint (Metric.closedBall T.center (2 * T.radius))
      (Metric.closedBall (A.center s) (A.radius s)))
    {g : ℂ → ℝ≥0∞}
    (D : ℕ → WeightedCollar base.physicalDomain π base.dust L.data.target g)
    (hnest : ∀ n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀ V ∈ 𝓝 L.data.target, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ V)
    (hanchor : Disjoint base.anchor (closure (D 0).region))
    (hfinite : OnePoint.infty ∉ closure (D 0).region)
    (hcontours : ∀ n, L.data.gateContours n = frontier (D n).region)
    (hgates : ∀ n, L.data.gateSets n = Subtype.val ''
      ((quotientNormalizedMap base.domainEquiv A.function) ⁻¹' closure T.openGate))
    (B R : ℝ) (hB : B / 4 < M.radius) (hR : 5 * M.radius < R)
    (hfar : ∀ z : ℂ, B ≤ ‖z‖ → π (z : Sphere) ∈ base.anchor) :
    ∃ c : SelectableMaskedCoordinate base π, c.CompatibleWith Candidates ∧
      Nonempty (MeanCoordinatePresentation hsch base π c.coordinate) ∧
      (c.coordinate.singular : Sphere) = σ s ∧
      ∃ W : MeanExclusionWitness c.coordinate A.function (A.plane_open_embedding hG).1
        (A.center s) ⟨A.radius s, (A.bounds s).2.1⟩ R,
        (∀ z ∈ frontier (jordanInterior W.disk), ‖z‖ < B) ∧
        ((finiteSourceMap A.function (A.plane_open_embedding hG).1,
          A.center s, (⟨A.radius s, (A.bounds s).2.1⟩ : ℝ≥0)), M.radius) ∈
            W.sizedNeighborhood (B / 4) := by
  have hR0 : 0 ≤ R := (mul_nonneg (by norm_num) M.radius_pos.le).trans hR.le
  obtain ⟨δ, _, F₀, hF₀, hEq, K, hevent⟩ := L.eventually_protrusion_mean
    hsch hsep hcoarea hcollar hselect harcs hG hU hdense hdust hπ hclosed hsurj hr he hbad
    hp E T hq s hqs hseparated hR0 D hnest hshrink hanchor hfinite hcontours hgates
  obtain ⟨n, J, hJ, Q, ⟨N⟩⟩ := hevent.exists
  have hbJ : L.data.target ∈ ((↑) : ℂ → Sphere) '' jordanInterior J :=
    hJ ▸ (D n).point_mem_region hsurj hp
  obtain ⟨c, hc, hcomp, hpres, _, _⟩ := N.selectable rank hrank hcoarea hsard hsch hsep
    base hG hU hdense hdust π hπ hclosed hsurj hr hTD hbad Flags hFlags hFlagsB
    C presentation hlevel hweights hmarked hsingular hP hunique ω L hLusin hfiber harcs
    previous hprevious Q hbJ hweighted he Candidates label
    (fun c hc x hx => Or.inl (hflags c hc hx)) hgraphs
  refine ⟨c, hcomp, hpres, ?_, ?_⟩
  · rw [hc, N.singular_eq, htarget]
  · rw [hc]
    let W := N.exclusion.congr_map (hF₁ := (A.plane_open_embedding hG).1) hEq
    have hanti : Antitone (fun n => (D n).region) :=
      antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
    have hNJ : Disjoint base.anchor (((↑) : ℂ → Sphere) '' jordanInterior J) := by
      rw [← hJ]
      exact hanchor.mono_right ((hanti (Nat.zero_le n)).trans subset_closure)
    refine ⟨W, ?_, W.mem_sizedNeighborhood hB hR⟩
    exact N.boundary_norm_lt_of_anchor hNJ hfar

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean_oai.{u_1, u_2} := @OAI.CircleDomainRigidity.RecursiveCodeLaw.exists_selectable_protrusion_mean_oai.{u_1, u_2}
