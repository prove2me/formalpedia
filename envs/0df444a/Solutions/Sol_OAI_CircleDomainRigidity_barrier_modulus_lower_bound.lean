-- Prove2me | solution 1 for OAI.CircleDomainRigidity.barrier_modulus_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:48:13.885858+00:00
-- url     : https://prove2.me/submissions/afa4a005-d5e8-4e55-9521-03e69944e787

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C008
import Theorems.Thm_OAI_CircleDomainRigidity_exists_filled_first_arrival_barrier_potential

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
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem visitCount_ge_nat {γ : C(PathTime, X)} {x : X} {n : ℕ}
    (h : (γ, x) ∈ visitAtLeastSet n) : (n : ℝ≥0∞) ≤ visitCount γ x := by
  classical
  calc
    (n : ℝ≥0∞) = (if (γ, x) ∈ visitAtLeastSet n then (n : ℝ≥0∞) else 0) :=
      (ite_eq_left h).symm
    _ ≤ visitCount γ x := le_iSup (fun k : ℕ =>
      if (γ, x) ∈ visitAtLeastSet k then (k : ℝ≥0∞) else 0) n

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_VisitCardinality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measurable finite-witness count agrees with the actual extended sum
of unit tolls over all visit times. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem visitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    visitCount γ x = ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 := by
  classical
  apply le_antisymm
  · unfold visitCount
    apply iSup_le
    intro n
    split
    · rename_i hn
      obtain ⟨t, ht, heq⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if γ (t i) = x then (1 : ℝ≥0∞) else 0 := by
          simp only [heq, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ ∑' t : PathTime, if γ t = x then (1 : ℝ≥0∞) else 0 :=
          ENNReal.tsum_comp_le_tsum_of_injective ht (fun t => if γ t = x then 1 else 0)
    · exact bot_le
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (fun t => γ t = x)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have ht : (γ, x) ∈ visitAtLeastSet (Fintype.card E) := by
      refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
      intro i
      exact (Finset.mem_filter.mp (e i).property).2
    have hb := visitCount_ge_nat ht
    simpa only [Finset.sum_boole, Fintype.card_coe] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotTupleMeasure_univ_le (s : TagSlot) : slotTupleMeasure s univ ≤ 1 := by
  cases s with
  | inl u => simp [slotTupleMeasure]
  | inr q => simp [slotTupleMeasure]

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem tsum_slotWeight : ∑' k, slotWeight k = 2 := ENNReal.tsum_geometric_two

theorem weightedTupleMeasure_apply (θ : ℕ → TagSlot) {s : Set LevelTuple}
    (hs : MeasurableSet s) :
    weightedTupleMeasure θ s = ∑' k, slotWeight k * slotTupleMeasure (θ k) s := by
  simp only [weightedTupleMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

theorem weightedTupleMeasure_mass_le (θ : ℕ → TagSlot) : weightedTupleMeasure θ univ ≤ 2 := by
  rw [weightedTupleMeasure_apply θ MeasurableSet.univ, ← tsum_slotWeight]
  exact ENNReal.tsum_le_tsum fun k =>
    mul_le_of_le_one_right (bot_le) (slotTupleMeasure_univ_le (θ k))

instance instIsFiniteMeasureLevelTupleWeightedTupleMeasure (θ : ℕ → TagSlot) : IsFiniteMeasure (weightedTupleMeasure θ) :=
  ⟨lt_of_le_of_lt (weightedTupleMeasure_mass_le θ) (by norm_num)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem lintegral_pathOccupation (γ : RectifiablePath X) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂pathOccupation γ = ∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ :=
  lintegral_map hg γ.val.continuous.measurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalDyadicLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

variable [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem physicalStageOccupation_univ (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞) (n : ℕ) :
    physicalStageOccupation e y₀ n γ univ = physicalStageLength e y₀ n γ := by
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableOccupationCode_univ (physicalDyadicPath_rectifiable e y₀ hγ n _)]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DyadicPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel limit of the increasing dyadic physical occupation measures.
Its mass is the dyadic domain-length functional, and it is supported in the
physical domain. `PhysicalLengthCharacterization` identifies the associated
time measure with compact-interval arclength and componentwise exhaustion. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem dyadicPhysicalOccupation_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set Y} (hs : MeasurableSet s) :
    dyadicPhysicalOccupation e y₀ γ s = ⨆ n, physicalStageOccupation e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem dyadicPhysicalOccupation_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [dyadicPhysicalOccupation_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageOccupation_univ e y₀ γ.property]
  rfl

instance instIsFiniteMeasureDyadicPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (dyadicPhysicalOccupation e y₀ γ) :=
  ⟨by rw [dyadicPhysicalOccupation_univ]; exact γ.property⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationPushforward
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation is the pushforward of domain-time arclength, with
parameter multiplicity retained. The value assigned at dust times is irrelevant. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalValue_subpath (e : G ≃ₜ U) (y₀ : Y)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    {t : PathTime} (ht : t ∈ Icc a b) :
    physicalValue e y₀ (γ.val t) = physicalSubpath e hab γ t := by
  simp only [physicalValue, dite_eq_left (γ.property ht), physicalSubpath,
    ContinuousMap.coe_mk, timeClip, min_eq_right ht.2, max_eq_right ht.1]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SparseTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite individual tuple costs suffice for arbitrarily small total cost
after an injective reassignment of slots. No summability of the original
weighted tuple costs is required. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem lintegral_weightedTupleMeasure (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞) :
    ∫⁻ t, f t ∂weightedTupleMeasure θ =
      ∑' k, slotWeight k * ∫⁻ t, f t ∂slotTupleMeasure (θ k) := by
  rw [weightedTupleMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

theorem lintegral_weightedTupleMeasure_sparse (e : ℕ ↪ ℕ)
    (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞) :
    ∫⁻ t, f t ∂weightedTupleMeasure (sparseTags e θ) =
      ∑' i, slotWeight (e i) * ∫⁻ t, f t ∂slotTupleMeasure (θ i) := by
  rw [lintegral_weightedTupleMeasure]
  let F := fun k => slotWeight k * ∫⁻ t, f t ∂slotTupleMeasure (sparseTags e θ k)
  have hs : Function.support F ⊆ Set.range e := by
    intro k hk
    by_contra hnot
    apply hk
    simp only [F, sparseTags_outside e θ hnot, inactiveTag, slotTupleMeasure,
      Sum.elim_inl, lintegral_zero_measure, mul_zero]
  calc
    ∑' k, F k = ∑' i, F (e i) := (e.injective.tsum_eq hs).symm
    _ = _ := by simp only [F, sparseTags_at]

theorem slotWeight_antitone : Antitone slotWeight := by
  intro n m hnm
  exact pow_le_pow_right_of_le_one' (by norm_num) hnm

theorem exists_sparse_weighted_sum_le (a : ℕ → ℝ≥0∞) (ha : ∀ k, a k < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, (∑' k, slotWeight (e k) * a k) ≤ ε := by
  have hex : ∀ k, ∃ n, slotWeight n * a k < (ε / 2) * slotWeight k := by
    intro k
    have ht : 0 < (ε / 2) * slotWeight k :=
      ENNReal.mul_pos (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩).ne'
        (slotWeight_pos k).ne'
    have hw : Tendsto slotWeight atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hc : Tendsto (fun n => slotWeight n * a k) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const hw (Or.inr (ne_of_lt (ha k)))
    exact ((tendsto_order.mp hc).2 _ ht).exists
  choose n hn using hex
  let e : ℕ ↪ ℕ := ⟨fun k => Nat.pair k (n k), fun i j hij => (Nat.pair_eq_pair.mp hij).1⟩
  refine ⟨e, ?_⟩
  calc
    ∑' k, slotWeight (e k) * a k ≤ ∑' k, (ε / 2) * slotWeight k := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact le_trans (mul_le_mul' (slotWeight_antitone (Nat.right_le_pair k (n k))) le_rfl)
        (hn k).le
    _ = (ε / 2) * 2 := by rw [ENNReal.tsum_mul_left, tsum_slotWeight]
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem exists_sparse_tuple_cost_le (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞)
    (hf : ∀ k, (∫⁻ t, f t ∂slotTupleMeasure (θ k)) < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, (∫⁻ t, f t ∂weightedTupleMeasure (sparseTags e θ)) ≤ ε := by
  obtain ⟨e, he⟩ := exists_sparse_weighted_sum_le _ hf hε
  exact ⟨e, by rwa [lintegral_weightedTupleMeasure_sparse]⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Visit multiplicities with the terminal parameter omitted. The extended
subtraction formula is justified by an exact all-time sum decomposition. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preterminalVisitCount_eq_tsum (γ : C(PathTime, X)) (x : X) :
    preterminalVisitCount γ x =
      ∑' t : PathTime, if t ≠ ⊤ ∧ γ t = x then (1 : ℝ≥0∞) else 0 := by
  rw [preterminalVisitCount, visitCount_eq_tsum, ENNReal.tsum_eq_add_tsum_ite ⊤]
  have hfinite : terminalVisitCount γ x ≠ ∞ := by
    unfold terminalVisitCount
    split <;> simp
  change terminalVisitCount γ x + _ - terminalVisitCount γ x = _
  rw [ENNReal.add_sub_cancel_left hfinite]
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht]


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AtomicVisitMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable atomic part of a path's coding measure, using actual
preterminal visit multiplicity and prescribed positive point weights. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X D : Type*} [MetricSpace X] [MeasurableSpace D]

theorem atomicVisitMeasure_apply (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X))
    {A : Set D} (hA : MeasurableSet A) :
    atomicVisitMeasure p c γ A =
      ∑' s, (c s * preterminalVisitCount γ (p s)) * A.indicator 1 s := by
  simp only [atomicVisitMeasure, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hA]

theorem atomicVisitMeasure_univ (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X)) :
    atomicVisitMeasure p c γ univ = ∑' s, c s * preterminalVisitCount γ (p s) := by
  simp only [atomicVisitMeasure_apply p c γ MeasurableSet.univ, indicator_univ,
    Pi.one_apply, mul_one]

theorem lintegral_atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X))
    (f : D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂atomicVisitMeasure p c γ =
      ∑' s, (c s * preterminalVisitCount γ (p s)) * f s := by
  rw [atomicVisitMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathCostMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual three-part coding measure: physical occupation, countable
preterminal visits, and weighted tuples. Finiteness is a Borel code condition. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costPhysical : Measurable (costPhysical (Y := Y) (D := D)) := by
  have hc : Continuous (costPhysical (Y := Y) (D := D)) := continuous_inl
  exact Continuous.measurable (α := Y) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costAtomic : Measurable (costAtomic (Y := Y) (D := D)) := by
  have hc : Continuous (costAtomic (Y := Y) (D := D)) := continuous_inr.comp continuous_inl
  exact Continuous.measurable (α := D) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costTuple : Measurable (costTuple (Y := Y) (D := D)) := by
  have hc : Continuous (costTuple (Y := Y) (D := D)) := continuous_inr.comp continuous_inr
  exact Continuous.measurable (α := LevelTuple) (γ := PathCostSpace Y D) hc

instance instIsFiniteMeasureBaseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : IsFiniteMeasure (baseCodeOccupation d Γ) := by
  unfold baseCodeOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem baseCodeOccupation_univ (d : PathCodeData X Y) (Γ : BasePathCode d) :
    baseCodeOccupation d Γ univ = physicalDomainLength d.domainEquiv d.basePoint Γ.val.1 :=
  dyadicPhysicalOccupation_univ _ _ _

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_univ (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) :
    pathCostMeasure d p c Γ univ =
      physicalDomainLength d.domainEquiv d.basePoint Γ.val.1 +
      (∑' s, c s * preterminalVisitCount Γ.val.1 (p s)) + weightedTupleMeasure Γ.val.2 univ := by
  simp only [pathCostMeasure, Measure.add_apply,
    Measure.map_apply measurable_costPhysical MeasurableSet.univ,
    Measure.map_apply measurable_costAtomic MeasurableSet.univ,
    Measure.map_apply measurable_costTuple MeasurableSet.univ,
    preimage_univ, baseCodeOccupation_univ, atomicVisitMeasure_univ]

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_finite_iff (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) :
    pathCostMeasure d p c Γ univ < ∞ ↔
      (∑' s, c s * preterminalVisitCount Γ.val.1 (p s)) < ∞ := by
  rw [pathCostMeasure_univ]
  have hp := Γ.property.1.1
  have ht := measure_lt_top (weightedTupleMeasure Γ.val.2) univ
  simp only [ENNReal.add_lt_top, hp, ht, true_and, and_true]

variable [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [SecondCountableTopology X] [Countable D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem lintegral_pathCostMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (f : PathCostSpace Y D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂pathCostMeasure d p c Γ =
      (∫⁻ y, f (costPhysical y) ∂baseCodeOccupation d Γ) +
      (∑' s, (c s * preterminalVisitCount Γ.val.1 (p s)) * f (costAtomic s)) +
      ∫⁻ t, f (costTuple t) ∂weightedTupleMeasure Γ.val.2 := by
  rw [pathCostMeasure, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hf measurable_costPhysical, lintegral_map hf measurable_costAtomic,
    lintegral_map hf measurable_costTuple]
  rw [lintegral_atomicVisitMeasure p c Γ.val.1 (fun s => f (costAtomic s))
    (hf.comp measurable_costAtomic)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SparseBaseCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Injective retagging preserves the complete base-code conditions and cost finiteness.
It is a Borel operation on the actual code space. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

variable [BorelSpace C(PathTime, X)]

variable {D : Type*} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem baseCodeOccupation_sparse (d : PathCodeData X Y) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) :
    baseCodeOccupation d (sparseBaseCode d e Γ) = baseCodeOccupation d Γ := rfl

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_sparse_finite_iff (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) :
    pathCostMeasure d p c (sparseBaseCode d e Γ) univ < ∞ ↔
      pathCostMeasure d p c Γ univ < ∞ := by
  rw [pathCostMeasure_finite_iff, pathCostMeasure_finite_iff]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleExclusions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Excluding precisely the infinite tuple values makes every individual
slot integral finite. The exclusions remain Borel for a Borel metric. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem active_mem_tupleInfiniteExclusions (f : LevelTuple → ℝ≥0∞) (q : TagData)
    (hq : f (tagDataTuple q) = ∞) :
    activeTagSlot q ∈ tagTupleExcluded (tupleInfiniteExclusions f) := by
  apply mem_iUnion.mpr
  refine ⟨q.1, mem_iUnion.mpr ⟨q.2.1, ?_⟩⟩
  refine ⟨q.2.2, ⟨hq, mem_univ _⟩, ?_⟩
  rfl

theorem slotIntegral_finite_of_excluded {f : LevelTuple → ℝ≥0∞} (hf : Measurable f)
    {s : TagSlot} (hs : s ∉ tagTupleExcluded (tupleInfiniteExclusions f)) :
    (∫⁻ t, f t ∂slotTupleMeasure s) < ∞ := by
  cases s with
  | inl u => simp [slotTupleMeasure]
  | inr q =>
    rw [slotTupleMeasure, Sum.elim_inr, lintegral_dirac' _ hf]
    exact lt_top_iff_ne_top.mpr fun hq => hs (active_mem_tupleInfiniteExclusions f q hq)

theorem tagRules_slotIntegral_finite {X : Type*} [MetricSpace X]
    {H : ℕ → Set (UnitAddCircle × X)} {f : LevelTuple → ℝ≥0∞}
    (hf : Measurable f) {Γ : TaggedPath X}
    (hΓ : TagRules H (tupleInfiniteExclusions f) Γ) (k : ℕ) :
    (∫⁻ t, f t ∂slotTupleMeasure (Γ.2 k)) < ∞ :=
  slotIntegral_finite_of_excluded hf (hΓ k).2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RetaggedCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The auxiliary tuple cost can be removed from an admissible metric's
lower bound. This is the retagging step in Section 4 of the manuscript. -/

open Set MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)]

theorem pathCostIntegral_sparse (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (e : ℕ ↪ ℕ) :
    (∫⁻ z, h z ∂pathCostMeasure d p c (sparseBaseCode d e Γ)) =
      nonTupleCost d p c Γ h +
        ∫⁻ t, h (costTuple t) ∂weightedTupleMeasure (sparseTags e Γ.val.2) := by
  rw [lintegral_pathCostMeasure d p c _ h hh, baseCodeOccupation_sparse]
  rfl

theorem exists_endpointCode_small_tuple (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ,
      EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple))
        (sparseBaseCode d e Γ).val ∧
      (∫⁻ z, h z ∂pathCostMeasure d p c (sparseBaseCode d e Γ)) ≤
        nonTupleCost d p c Γ h + ε := by
  obtain ⟨e, he⟩ := exists_sparse_tuple_cost_le Γ.val.2 (h ∘ costTuple)
    (tagRules_slotIntegral_finite (hh.comp measurable_costTuple) hΓ.1.2.1) hε
  refine ⟨e, endpointCode_sparse d ν _ e hΓ, ?_⟩
  rw [pathCostIntegral_sparse d p c Γ h hh]
  exact add_le_add le_rfl he

theorem nonTupleCost_ge_one_of_admissible (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hfinite : pathCostMeasure d p c Γ univ < ∞)
    (hadm : CostAdmissible d p c ν h) : 1 ≤ nonTupleCost d p c Γ h := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨e, he, hcost⟩ := exists_endpointCode_small_tuple d p c ν Γ h hh
    hΓ (ENNReal.coe_pos.mpr hε)
  exact (hadm (sparseBaseCode d e Γ)
    ((pathCostMeasure_sparse_finite_iff d p c e Γ).mpr hfinite) he.1.2.2.2.2).trans hcost

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True boundary tolls with exactly the final parameter omitted, retaining
all multiplicities at earlier times. Positive added weights control code mass. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preterminalToll_eq_visits (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m = ∑' x, m x * preterminalVisitCount γ x := by
  rw [preterminalToll, ← ENNReal.tsum_fiberwise (fun t => if t = ⊤ then 0 else m (γ t)) γ]
  apply tsum_congr
  intro x
  rw [preterminalVisitCount_eq_tsum, ← ENNReal.tsum_mul_left,
    tsum_subtype (γ ⁻¹' {x}) (fun t : PathTime => if t = ⊤ then 0 else m (γ t))]
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> by_cases hx : γ t = x <;> simp [ht, hx, Set.indicator]

theorem weighted_preterminal_sum_le {D : Type*} (γ : C(PathTime, X)) (p : D → X)
    {c m : D → ℝ≥0∞} {δ : ℝ≥0∞} (hm : ∀ s, δ * c s ≤ m s) :
    δ * (∑' s, c s * preterminalVisitCount γ (p s)) ≤
      ∑' s, m s * preterminalVisitCount γ (p s) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  rw [← mul_assoc]
  exact mul_le_mul' (hm s) le_rfl

theorem finite_preterminal_sum_of_positive_tolls {D : Type*}
    (γ : C(PathTime, X)) (p : D → X) {c m : D → ℝ≥0∞} {δ : ℝ≥0∞}
    (hδ : 0 < δ) (hm : ∀ s, δ * c s ≤ m s)
    (hfinite : (∑' s, m s * preterminalVisitCount γ (p s)) < ∞) :
    (∑' s, c s * preterminalVisitCount γ (p s)) < ∞ := by
  by_contra h
  have he : (∑' s, c s * preterminalVisitCount γ (p s)) = ∞ :=
    top_unique (not_lt.mp h)
  have hb := lt_of_le_of_lt (weighted_preterminal_sum_le γ p hm) hfinite
  simp only [he, ENNReal.mul_top hδ.ne', lt_self_iff_false] at hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_AdmissiblePathCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive perturbation of an admissible coding metric gives a genuine
physical-plus-preterminal cost lower bound on every allowed path. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSpace C(PathTime, X)]

omit [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D] in
theorem nonTupleCost_le_physicalAtomicCost (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (Γ : BasePathCode d)
    (h : PathCostSpace Y D → ℝ≥0∞) (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞)
    (hg : ∀ y, h (costPhysical y) ≤ g y)
    (hm : ∀ s, c s * h (costAtomic s) ≤ m s) :
    nonTupleCost d p c Γ h ≤ physicalAtomicCost d p Γ g m := by
  apply add_le_add (lintegral_mono hg)
  apply ENNReal.tsum_le_tsum
  intro s
  calc
    (c s * preterminalVisitCount Γ.val.1 (p s)) * h (costAtomic s) =
        (c s * h (costAtomic s)) * preterminalVisitCount Γ.val.1 (p s) := by ac_rfl
    _ ≤ m s * preterminalVisitCount Γ.val.1 (p s) := mul_le_mul' (hm s) le_rfl

theorem finite_code_of_physicalAtomicCost (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (Γ : BasePathCode d)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) {δ : ℝ≥0∞}
    (hδ : 0 < δ) (hm : ∀ s, δ * c s ≤ m s)
    (hcost : physicalAtomicCost d p Γ g m < ∞) :
    pathCostMeasure d p c Γ univ < ∞ := by
  rw [pathCostMeasure_finite_iff]
  apply finite_preterminal_sum_of_positive_tolls Γ.val.1 p hδ hm
  exact lt_of_le_of_lt le_add_self hcost

theorem physicalAtomicCost_ge_one (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) (Γ : BasePathCode d)
    (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hadm : CostAdmissible d p c ν h)
    (g : Y → ℝ≥0∞) (m : D → ℝ≥0∞) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hg : ∀ y, h (costPhysical y) ≤ g y)
    (hm : ∀ s, c s * h (costAtomic s) ≤ m s)
    (hpos : ∀ s, δ * c s ≤ m s) :
    1 ≤ physicalAtomicCost d p Γ g m := by
  by_cases hfinite : physicalAtomicCost d p Γ g m < ∞
  · exact (nonTupleCost_ge_one_of_admissible d p c ν Γ h hh hΓ
      (finite_code_of_physicalAtomicCost d p c Γ g m hδ hpos hfinite) hadm).trans
      (nonTupleCost_le_physicalAtomicCost d p c Γ h g m hg hm)
  · rw [top_unique (not_lt.mp hfinite)]
    exact le_top

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
-- module Solutions.Q146_CD.CircleDomains_Probability_SimpleArcDomainDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Along a simple arc, domain points are dense when the complementary
dust is totally disconnected. -/

open Set Function
open scoped Topology
namespace CircleDomainRigidity

theorem simple_arc_domain_preimage_dense
    {X : Type*} [TopologicalSpace X] {U B : Set X}
    (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (γ : unitInterval → X) (hγ : Continuous γ) (hinj : Injective γ) :
    Dense (γ ⁻¹' U) := by
  apply dense_of_exists_between
  intro a b hab
  by_contra hn
  push Not at hn
  have hsub : γ '' Ioo a b ⊆ B := by
    rintro z ⟨t, ht, rfl⟩
    by_contra htB
    exact hn t (hBU htB) ht
  have hsingle := hB (γ '' Ioo a b) hsub
    (isPreconnected_Ioo.image γ hγ.continuousOn)
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have heq : γ c = γ d := hsingle ⟨c, ⟨hac, hcb⟩, rfl⟩
    ⟨d, ⟨hac.trans hcd, hdb⟩, rfl⟩
  exact hcd.ne (hinj heq)

theorem simple_arc_point_mem_closure_domain
    {X : Type*} [TopologicalSpace X] {U B : Set X}
    (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (γ : unitInterval → X) (hγ : Continuous γ) (hinj : Injective γ) (t : unitInterval) :
    γ t ∈ closure (range γ ∩ U) := by
  have hd := simple_arc_domain_preimage_dense hB hBU γ hγ hinj
  have ht : t ∈ closure (γ ⁻¹' U) := by rw [hd.closure_eq]; trivial
  have him := image_closure_subset_closure_image hγ ⟨t, ht, rfl⟩
  apply closure_mono (fun z hz => ?_) him
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨mem_range_self s, hs⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ArcBoundaryPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pass the actual path inequality to free boundary traces along a
simple arc. Only approximation by domain points is used. -/

open Set Function Filter
open scoped Topology
namespace CircleDomainRigidity

theorem trace_payment_of_domain_closure
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {S U : Set X} (hSU : S ⊆ U) {x y : X}
    (hx : x ∈ closure S) (hy : y ∈ closure S)
    (u : X → ℝ) {a b A : ℝ}
    (ha : Tendsto u (𝓝[U] x) (𝓝 a)) (hb : Tendsto u (𝓝[U] y) (𝓝 b))
    (hpay : ∀p ∈ S, ∀q ∈ S, |u p - u q| ≤ A) : |a - b| ≤ A := by
  obtain ⟨p, hp, hpx⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨q, hq, hqy⟩ := mem_closure_iff_seq_limit.mp hy
  have hpU : Tendsto p atTop (𝓝[U] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpx, Eventually.of_forall (fun n => hSU (hp n))⟩
  have hqU : Tendsto q atTop (𝓝[U] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqy, Eventually.of_forall (fun n => hSU (hq n))⟩
  have hlim : Tendsto (fun n => |u (p n) - u (q n)|) atTop (𝓝 |a - b|) :=
    ((ha.comp hpU).sub (hb.comp hqU)).abs
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => hpay _ (hp n) _ (hq n)))

theorem simple_arc_boundary_payment
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {U B : Set X} (hB : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    {x y : X} (γ : Path x y) (hinj : Injective γ)
    (u : X → ℝ) {a b A : ℝ}
    (ha : Tendsto u (𝓝[U] x) (𝓝 a)) (hb : Tendsto u (𝓝[U] y) (𝓝 b))
    (hpay : ∀p ∈ range γ ∩ U, ∀q ∈ range γ ∩ U, |u p - u q| ≤ A) :
    |a - b| ≤ A := by
  apply trace_payment_of_domain_closure inter_subset_right ?_ ?_ u ha hb hpay
  · simpa only [γ.source] using
      simple_arc_point_mem_closure_domain hB hBU γ γ.continuous hinj 0
  · simpa only [γ.target] using
      simple_arc_point_mem_closure_domain hB hBU γ γ.continuous hinj 1

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TupleReference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tuple reference measure is a positive weighted sum of Lebesgue
measures on the finite tuple tori, indexed by label type rather than slot. -/

open Set MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem continuous_tupleFiber (i : TupleType) : Continuous (tupleFiber i) :=
  continuous_sigmaMk.comp (continuous_const.prodMk continuous_id)

theorem measurable_tupleFiber (i : TupleType) : Measurable (tupleFiber i) :=
  Continuous.measurable (α := Fin (i.1 + 1) → UnitAddCircle) (γ := LevelTuple)
    (continuous_tupleFiber i)

theorem tupleReference_apply (ω : TupleType → ℝ≥0∞)
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    tupleReference ω A = ∑' i, ω i * volume (tupleFiber i ⁻¹' A) := by
  simp only [tupleReference, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_tupleFiber _) hA]

theorem tupleReference_fiber_null {ω : TupleType → ℝ≥0∞}
    (hω : ∀ i, ω i ≠ 0) {A : Set LevelTuple} (hA : MeasurableSet A)
    (hnull : tupleReference ω A = 0) (i : TupleType) :
    volume (tupleFiber i ⁻¹' A) = 0 := by
  rw [tupleReference_apply ω hA, ENNReal.tsum_eq_zero] at hnull
  exact (mul_eq_zero.mp (hnull i)).resolve_left (hω i)

theorem null_tupleInfiniteExclusions {ω : TupleType → ℝ≥0∞}
    (hω : ∀ i, ω i ≠ 0) {f : LevelTuple → ℝ≥0∞} (hf : Measurable f)
    (hint : (∫⁻ t, f t ^ 2 ∂tupleReference ω) < ∞) (n : ℕ) (l : Fin (n + 1) → ℕ) :
    volume (tupleInfiniteExclusions f n l) = 0 := by
  have hae : ∀ᵐ t ∂tupleReference ω, f t < ∞ := by
    filter_upwards [ae_lt_top (hf.pow_const 2) hint.ne] with t ht
    by_contra hn
    have he : f t = ∞ := top_unique (not_lt.mp hn)
    simp [he] at ht
  have hnull : tupleReference ω {t | f t = ∞} = 0 := by
    simpa only [ae_iff, not_lt, top_le_iff] using hae
  exact tupleReference_fiber_null hω (hf (measurableSet_singleton ∞)) hnull ⟨n, l⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathCostReference
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite reference measure for modulus: physical area, squared
countable-point weights, and the weighted tuple tori. Its square integral
is exactly the sum of the three corresponding energies. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

omit [TopologicalSpace D] [BorelSpace D] in
theorem lintegral_atomicReference (c : D → ℝ≥0∞) (f : D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂atomicReference c = ∑' s, (c s) ^ 2 * f s := by
  rw [atomicReference, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

theorem lintegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ∂μ) +
      (∑' s, (c s) ^ 2 * h (costAtomic s)) + ∫⁻ t, h (costTuple t) ∂τ := by
  rw [pathCostReference, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hh measurable_costPhysical, lintegral_map hh measurable_costAtomic,
    lintegral_map hh measurable_costTuple]
  rw [lintegral_atomicReference c (fun s => h (costAtomic s)) (hh.comp measurable_costAtomic)]

theorem squareIntegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ^ 2 ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ^ 2 ∂μ) +
      (∑' s, (c s * h (costAtomic s)) ^ 2) + ∫⁻ t, h (costTuple t) ^ 2 ∂τ := by
  rw [lintegral_pathCostReference μ c τ _ (hh.pow_const 2)]
  simp only [mul_pow]

theorem null_tupleExclusions_of_reference_energy (μ : Measure Y) (c : D → ℝ≥0∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0)
    (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hint : (∫⁻ z, h z ^ 2 ∂pathCostReference μ c (tupleReference ω)) < ∞)
    (n : ℕ) (l : Fin (n + 1) → ℕ) :
    volume (tupleInfiniteExclusions (h ∘ costTuple) n l) = 0 := by
  apply null_tupleInfiniteExclusions hω (hh.comp measurable_costTuple)
  rw [squareIntegral_pathCostReference μ c (tupleReference ω) h hh] at hint
  exact lt_of_le_of_lt le_add_self hint

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CountableVisitNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the terminal visit adds at most one to the counting square
norm. The estimate is independent of the auxiliary positive atomic weights. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem countingSquareNorm_add_le {D : Type*} [Countable D] (a b : D → ℝ≥0∞) :
    countingSquareNorm (a + b) ≤ countingSquareNorm a + countingSquareNorm b := by
  let : MeasurableSpace D := ⊤
  have h := ENNReal.lintegral_Lp_add_le (μ := Measure.count)
    (p := (2 : ℝ)) (measurable_of_countable a).aemeasurable
    (measurable_of_countable b).aemeasurable (by norm_num)
  simpa only [ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeBarycenterDensities
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three components of a coding barycenter have the restrictions
of its density. Their square energies are bounded by the total energy. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] [Countable D] in
theorem codeReference_component_energies (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ y, q (costPhysical y) ^ 2 ∂μ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ ∧
      (∫⁻ t, q (costTuple t) ^ 2 ∂τ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ := by
  rw [squareIntegral_pathCostReference μ c τ q hq]
  exact ⟨le_add_of_le_left le_self_add, le_add_self⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CostPerturbation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive perturbations of the physical density and atomic tolls.
Their norm increase is controlled by the finite physical area and the
chosen square-summable countable weights. -/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

theorem squareIntegralNorm_add_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {f g : Y → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    squareIntegralNorm μ (f + g) ≤ squareIntegralNorm μ f + squareIntegralNorm μ g := by
  simpa only [squareIntegralNorm, ENNReal.rpow_two] using
    ENNReal.lintegral_Lp_add_le (μ := μ) (p := (2 : ℝ)) hf.aemeasurable hg.aemeasurable
      (by norm_num)

theorem squareIntegralNorm_const {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : ℝ≥0∞) :
    squareIntegralNorm μ (fun _ => δ) = δ * (μ univ) ^ (1 / 2 : ℝ) := by
  rw [squareIntegralNorm, lintegral_const,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have he : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [he]

theorem countingSquareNorm_mul {D : Type*} (δ : ℝ≥0∞) (c : D → ℝ≥0∞) :
    countingSquareNorm (fun s => δ * c s) = δ * countingSquareNorm c := by
  simp only [countingSquareNorm, mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have he : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [he]

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

theorem perturbedPhysicalDensity_norm (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    (δ : ℝ≥0∞) :
    squareIntegralNorm μ (perturbedPhysicalDensity h δ) ≤
      squareIntegralNorm (pathCostReference μ c τ) h + δ * (μ univ) ^ (1 / 2 : ℝ) := by
  have hs := squareIntegralNorm_add_le μ (hh.comp measurable_costPhysical)
    (measurable_const (a := δ))
  rw [squareIntegralNorm_const] at hs
  apply hs.trans
  apply add_le_add _ le_rfl
  exact ENNReal.rpow_le_rpow (codeReference_component_energies μ c τ h hh).1 (by norm_num)

variable [Countable D]

theorem perturbedAtomicToll_norm (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    (δ : ℝ≥0∞) :
    countingSquareNorm (perturbedAtomicToll h c δ) ≤
      squareIntegralNorm (pathCostReference μ c τ) h + δ * countingSquareNorm c := by
  have hs := countingSquareNorm_add_le (fun s => c s * h (costAtomic s)) (fun s => δ * c s)
  rw [countingSquareNorm_mul] at hs
  apply hs.trans
  apply add_le_add _ le_rfl
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [squareIntegral_pathCostReference μ c τ h hh]
  exact le_trans le_add_self le_self_add

theorem exists_small_positive_perturbation (μ : Measure Y) [IsFiniteMeasure μ]
    (c : D → ℝ≥0∞) (hc : (∑' s, c s ^ 2) < ∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      squareIntegralNorm μ (perturbedPhysicalDensity h δ) +
        countingSquareNorm (perturbedAtomicToll h c δ) ≤
      2 * squareIntegralNorm (pathCostReference μ c τ) h + ε := by
  let K : ℝ≥0∞ := (μ univ) ^ (1 / 2 : ℝ) + countingSquareNorm c
  have hK : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ),
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc.ne⟩
  obtain ⟨δ, hδ, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hK hε.ne'
  refine ⟨δ, hδ, ?_⟩
  have he := add_le_add (perturbedPhysicalDensity_norm μ c τ hh (δ : ℝ≥0∞))
    (perturbedAtomicToll_norm μ c τ hh (δ : ℝ≥0∞))
  calc
    _ ≤ (squareIntegralNorm (pathCostReference μ c τ) h + δ * (μ univ) ^ (1 / 2 : ℝ)) +
        (squareIntegralNorm (pathCostReference μ c τ) h + δ * countingSquareNorm c) := he
    _ = 2 * squareIntegralNorm (pathCostReference μ c τ) h + δ * K := by
      dsimp [K]
      rw [mul_add, two_mul]
      ac_rfl
    _ ≤ _ := add_le_add le_rfl hsmall.le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [Countable D] in
theorem perturbed_cost_ge_one (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hadm : CostAdmissible d p c ν h) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    1 ≤ physicalAtomicCost d p Γ (perturbedPhysicalDensity h δ) (perturbedAtomicToll h c δ) := by
  exact physicalAtomicCost_ge_one d p c ν Γ h hh hΓ hadm _ _ hδ
    (fun _ => le_self_add) (fun _ => le_self_add) (fun _ => le_add_self)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocallyFiniteL2Sum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! L² control of a pointwise finite sum by the sum of its local error
norms. This applies to the countable partition-of-unity error terms. -/

open Set Filter MeasureTheory Function
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem finiteSupport_hasSum_finsum {ι : Type*} (f : ι → ℝ)
    (hf : HasFiniteSupport f) : HasSum f (∑ᶠ i, f i) := by
  rw [← show (∑' i, f i) = ∑ᶠ i, f i from tsum_eq_finsum hf]
  exact (summable_of_hasFiniteSupport hf).hasSum

theorem aestronglyMeasurable_finsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    AEStronglyMeasurable (fun x => ∑ᶠ i, f i x) μ := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

theorem eLpNorm_finsum_le_tsum_of_pointFinite
    {ι : Type*} [Countable ι] (μ : Measure EuclideanPlane)
    (f : ι → EuclideanPlane → ℝ) (hf : ∀i, AEStronglyMeasurable (f i) μ)
    (hfin : ∀x, HasFiniteSupport (fun i => f i x)) :
    eLpNorm (fun x => ∑ᶠ i, f i x) 2 μ ≤ ∑' i, eLpNorm (f i) 2 μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (u := (atTop : Filter (Finset ι)))
    (f := fun s x => ∑ i ∈ s, f i x)
  · apply Eventually.of_forall
    intro s
    have h := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (f := f) (s := s) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have he : (fun x => ∑ i ∈ s, f i x) = ∑i ∈ s, f i := by
      ext x
      simp only [Finset.sum_apply]
    rw [he]
    exact h.trans (ENNReal.sum_le_tsum s)
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s (fun i _ => hf i)
  · exact Eventually.of_forall fun x => finiteSupport_hasSum_finsum _ (hfin x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSmoothPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth partition functions on an open planar domain. The
family is locally finite in the domain, allowing accumulation at its boundary. -/

open Set Function Filter TopologicalSpace
open scoped Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_openPlanePartition
    (Ω : Opens EuclideanPlane) (U : Ω → Set Ω) (hU : ∀x, U x ∈ 𝓝 x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (c : ι → Ω),
      ∀i, tsupport (ρ.weight i) ⊆ Subtype.val '' U (c i) := by
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨ι, b, hb⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓘(ℝ, EuclideanPlane)) (M := Ω) isClosed_univ (fun x _ => hU x)
  let : Encodable ι := b.locallyFinite.encodable (fun i => (b i).nonempty_support)
  let ρ := b.toSmoothPartitionOfUnity
  have hc (i : ι) : HasCompactSupport (ρ i) :=
    (b i).hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_mono (b.support_toSmoothPartitionOfUnity_subset i))
  let ψ : ι → EuclideanPlane → ℝ := fun i => Subtype.val.extend (ρ i) 0
  have hon (i : ι) (x : Ω) : ψ i x = ρ i x :=
    congrFun (Function.extend_comp Subtype.val_injective (ρ i) 0) x
  have hsub (i : ι) : tsupport (ψ i) ⊆ Subtype.val '' U (b.c i) := by
    apply ((hc i).tsupport_extend_zero_subset continuous_subtype_val).trans
    exact image_mono (hb.toSmoothPartitionOfUnity i)
  have hin (i : ι) : tsupport (ψ i) ⊆ Ω :=
    (hsub i).trans (image_subset_iff.mpr (fun x _ => x.property))
  have hsmooth (i : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) := by
    apply contMDiff_iff_contDiff.mp
    exact ContMDiff.extend_zero (hc i) (ρ i).contMDiff
  have hloc : LocallyFinite (fun i => Subtype.val ⁻¹' Function.support (ψ i) :
      ι → Set Ω) := by
    have heq : (fun i => Subtype.val ⁻¹' Function.support (ψ i) : ι → Set Ω) =
        fun i => Function.support (ρ i) := by
      funext i
      ext x
      simp only [mem_preimage, Function.mem_support, hon]
    rw [heq]
    exact ρ.locallyFinite
  have hn (i : ι) (x : EuclideanPlane) : 0 ≤ ψ i x := by
    by_cases hx : x ∈ Ω
    · rw [show x = ((⟨x, hx⟩ : Ω) : EuclideanPlane) from rfl, hon]
      exact ρ.nonneg i _
    · have hz : ψ i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hin i h))
      rw [hz]
  refine ⟨ι, inferInstance, ⟨ψ, hsmooth,
    fun i => (hc i).extend_zero continuous_subtype_val, hin, hloc, hn, ?_⟩, b.c, hsub⟩
  intro x
  simp only [hon]
  exact ρ.sum_eq_one (mem_univ x)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveMollification
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized smooth mollifiers preserve actual interval bounds and
constant plateaus. These are pointwise bounds on the input neighborhood. -/

open Set MeasureTheory Metric
open scoped Convolution

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem normed_convolution_eq_of_constant
    [HasContDiffBump E] (β : ContDiffBump (0 : E)) {u : E → ℝ} {x : E} {c : ℝ}
    (hc : ∀y ∈ ball x β.rOut, u y = c) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) = c := by
  rw [β.normed_convolution_eq_right (fun y hy => (hc y hy).trans
    (hc x (mem_ball_self β.rOut_pos)).symm)]
  exact hc x (mem_ball_self β.rOut_pos)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositiveSobolevApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

theorem planarMollification_tsupport_subset (u : EuclideanPlane → ℝ) (n : ℕ) :
    tsupport (planarMollification u n) ⊆
      Metric.cthickening (DeGiorgi.shrinkingBump (d := 2) n).rOut (tsupport u) := by
  have hs := support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (DeGiorgi.shrinkingBump (d := 2) n).normed volume) (g := u)
  apply closure_minimal (hs.trans ?_) Metric.isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at ha
  have ha' : ‖a‖ < (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  apply Metric.mem_cthickening_of_dist_le (x := a + b) (y := b)
    (δ := (DeGiorgi.shrinkingBump (d := 2) n).rOut) (tsupport u)
    (subset_tsupport u hb)
  simpa only [dist_eq_norm, add_sub_cancel_right] using ha'.le

theorem planarMollification_support_eventually {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hsub : tsupport u ⊆ Ω) : ∀ᶠ n in atTop, tsupport (planarMollification u n) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.isCompact.exists_cthickening_subset_open hΩ hsub
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn
  exact (planarMollification_tsupport_subset u n).trans
      ((Metric.cthickening_mono hn.le _).trans hδΩ)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMollifierSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem planarMollification_eq_on_compact_eventually
    {u : EuclideanPlane → ℝ} {K V : Set EuclideanPlane}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    {c : ℝ} (hc : ∀y ∈ V, u y = c) :
    ∀ᶠ n in atTop, ∀x ∈ K, planarMollification u n x = c := by
  filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn x hx
  exact normed_convolution_eq_of_constant volume (DeGiorgi.shrinkingBump n)
    (fun y hy => hc y (hn x hx hy))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactSobolevCutoff
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs turn local planar Sobolev functions into
global Sobolev functions, to which positive mollification applies. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem compact_cutoff_mem_Icc
    {Ω : Set EuclideanPlane} {u η : EuclideanPlane → ℝ}
    (hu : ∀x ∈ Ω, u x ∈ Icc 0 1) (hη : ∀x, η x ∈ Icc 0 1)
    (hsub : tsupport η ⊆ Ω) (x : EuclideanPlane) : η x * u x ∈ Icc 0 1 := by
  by_cases hx : x ∈ Ω
  · exact ⟨mul_nonneg (hη x).1 (hu x hx).1,
      (mul_le_mul (hη x).2 (hu x hx).2 (hu x hx).1 zero_le_one).trans_eq (one_mul 1)⟩
  · have hzero : η x = 0 := by
      by_contra hn
      exact hx (hsub (subset_tsupport η hn))
    simp only [hzero, zero_mul, mem_Icc, le_rfl, zero_le_one, and_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalSobolevSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
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

theorem exists_local_positive_sobolev_smoothing
    {Ω K : Set EuclideanPlane} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hunit : ∀x ∈ Ω, u x ∈ Icc 0 1) :
    ∃ (V : Set EuclideanPlane) (φ : ℕ → EuclideanPlane → ℝ),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ Ω ∧
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n) ∧
        ∀x, φ n x ∈ Icc 0 1) ∧
      (∀ᶠ n in atTop, tsupport (φ n) ⊆ Ω) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
        atTop (𝓝 0) ∧
      (∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
        2 (volume.restrict V)) atTop (𝓝 0)) ∧
      (∀W : Set EuclideanPlane, IsOpen W → K ⊆ W → ∀c : ℝ,
        (∀x ∈ W, u x = c) → ∀ᶠ n in atTop, ∀x ∈ K, φ n x = c) ∧
      (∀ᶠ n in atTop, ∀a b : ℝ, (∀x ∈ Ω, u x ∈ Icc a b) →
        ∀x ∈ K, φ n x ∈ Icc a b) := by
  obtain ⟨η, V, hη, hsη, hηunit, hsub, hV, hKV, hone⟩ :=
    exists_smooth_compact_cutoff_one_near hK hΩ hKΩ
  have hVΩ : V ⊆ Ω := by
    intro x hx
    apply hsub
    apply subset_tsupport η
    change η x ≠ 0
    rw [hone x hx]
    exact one_ne_zero
  let w : EuclideanPlane → ℝ := fun x => η x * u x
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hu.memW1p hη hsη hsub
  have hwunit : ∀x, w x ∈ Icc 0 1 := compact_cutoff_mem_Icc hunit hηunit hsub
  have hwLp : MemLp w 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hw_eq : EqOn w u V := fun x hx => by dsimp [w]; rw [hone x hx, one_mul]
  refine ⟨V, planarMollification w, hV, hKV, hVΩ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hwLp.locallyIntegrable (by norm_num)) n,
      planarMollification_hasCompactSupport hsη.mul_right n,
      planarMollification_mem_Icc hwLp.aestronglyMeasurable hwunit n⟩
  · exact planarMollification_support_eventually hsη.mul_right hΩ
      (tsupport_mul_subset_left.trans hsub)
  · have hl := tendsto_eLpNorm_restrict_zero (V := V) (planarMollification_tendsto_L2 hwLp)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [hw_eq hx]
  · intro i
    have hgi := weakGrad_eq_on_cutoff_plateau hV hVΩ hu hw hone i
    have hl := tendsto_eLpNorm_restrict_zero (V := V)
      (planarMollification_tendsto_gradient_L2 hw i)
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hgi] with x hx
    rw [hx]
  · intro W hW hKW c hc
    apply planarMollification_eq_on_compact_eventually hK (hV.inter hW)
      (subset_inter hKV hKW)
    intro x hx
    rw [hw_eq hx.1, hc x hx.2]
  · filter_upwards [planarMollifier_samples_eventually hK hV hKV] with n hn a b hab x hx
    apply normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hwLp.aestronglyMeasurable
    intro y hy
    have hyV := hn x hx hy
    rw [hw_eq hyV]
    exact hab y (hVΩ hyV)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevErrors
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative error estimates for multiplying local Sobolev
approximations by smooth partition functions. -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_mul_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) (hs : Function.support ψ ⊆ V) :
    AEStronglyMeasurable (fun x => ψ x * f x) volume := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi]
  exact (aestronglyMeasurable_indicator_iff hV).2 (hψ.aestronglyMeasurable.restrict.mul hf)

theorem eLpNorm_mul_le_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f ψ : EuclideanPlane → ℝ} (hf : AEStronglyMeasurable f (volume.restrict V))
    (hψ : Continuous ψ) {C : ℝ≥0} (hC : ∀x, ‖ψ x‖ ≤ C)
    (hs : Function.support ψ ⊆ V) :
    eLpNorm (fun x => ψ x * f x) 2 volume ≤ C * eLpNorm f 2 (volume.restrict V) := by
  have hi : V.indicator (fun x => ψ x * f x) = fun x => ψ x * f x := by
    funext x
    by_cases hx : x ∈ V
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, Function.notMem_support.mp (fun h => hx (hs h)), zero_mul]
  rw [← hi, eLpNorm_indicator_eq_eLpNorm_restrict hV]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
  exact Eventually.of_forall fun x => by
    have hnn : ‖ψ x‖₊ ≤ C := by exact_mod_cast hC x
    simpa only [Pi.mul_apply, nnnorm_mul] using mul_le_mul' hnn (le_refl ‖f x‖₊)

theorem tendsto_eLpNorm_mul_zero_of_support
    {V : Set EuclideanPlane} (hV : MeasurableSet V)
    {f : ℕ → EuclideanPlane → ℝ} (hf : ∀n, AEStronglyMeasurable (f n) (volume.restrict V))
    {ψ : EuclideanPlane → ℝ} (hψ : Continuous ψ) (hsψ : HasCompactSupport ψ)
    (hs : Function.support ψ ⊆ V)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ψ x * f n x) 2 volume) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := hψ.bounded_above_of_compact_support hsψ
  let C : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hC : ∀x, ‖ψ x‖ ≤ C := fun x => (hA x).trans (le_max_left _ _)
  have hl : Tendsto (fun n => (C : ℝ≥0∞) * eLpNorm (f n) 2 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) (fun n => eLpNorm_mul_le_of_support hV (hf n) hψ hC hs)

theorem tendsto_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {φ : ℕ → EuclideanPlane → ℝ} (hφ : ∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hv : Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 (volume.restrict V))
      atTop (𝓝 0))
    (hg : ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0))
    {ψ : EuclideanPlane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsψ : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      ψ x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (φ n x - u x)) 2 volume)
      atTop (𝓝 0) := by
  let dψ : EuclideanPlane → ℝ := fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsdψ : HasCompactSupport dψ := hsψ.fderiv_apply (𝕜 := ℝ) _
  have hsubdψ : Function.support dψ ⊆ V :=
    (subset_tsupport dψ).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)
  have hv' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => (hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
    hdψ hsdψ hsubdψ hv
  have hg' := tendsto_eLpNorm_mul_zero_of_support hV.measurableSet
    (fun n => ((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous hsψ ((subset_tsupport ψ).trans hsub) (hg i)
  have hl := hg'.add hv'
  simp only [zero_add] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le)
  intro n
  have key : ∀ {a b : EuclideanPlane → ℝ}, Function.support a ⊆ V → Continuous a →
      AEStronglyMeasurable b (volume.restrict V) → AEStronglyMeasurable (fun x => a x * b x) volume := by
    intro a b ha hac hb
    have he : (fun x => a x * b x) = V.indicator (fun x => a x * b x) := by
      funext x
      by_cases hx : x ∈ V
      · simp [hx]
      · have : a x = 0 := Function.notMem_support.mp (fun h => hx (ha h))
        simp [hx, this]
    rw [he]
    exact (aestronglyMeasurable_indicator_iff hV.measurableSet).mpr
      (hac.aestronglyMeasurable.restrict.mul hb)
  exact eLpNorm_add_le
    (key ((subset_tsupport ψ).trans hsub) hψ.continuous
      (((hφ n).continuous_fderiv (by simp)).clm_apply continuous_const
        |>.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable))
    (key hsubdψ hdψ ((hφ n).continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable))
    (by norm_num)
theorem aestronglyMeasurable_partition_derivative_error
    {V : Set EuclideanPlane} (hV : IsOpen V)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u V)
    {v ψ : EuclideanPlane → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsub : tsupport ψ ⊆ V) (i : Fin 2) :
    AEStronglyMeasurable (fun x =>
      ψ x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) - hu.weakGrad x i) +
      (fderiv ℝ ψ x) (EuclideanSpace.single i 1) * (v x - u x)) volume := by
  have hdv : Continuous (fun x => (fderiv ℝ v x) (EuclideanSpace.single i 1)) :=
    (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (aestronglyMeasurable_mul_of_support hV.measurableSet
    (hdv.aestronglyMeasurable.restrict.sub (hu.weakGrad_component_memLp i).aestronglyMeasurable)
    hψ.continuous ((subset_tsupport ψ).trans hsub)).add
      (aestronglyMeasurable_mul_of_support hV.measurableSet
        (hv.continuous.aestronglyMeasurable.restrict.sub hu.memLp.aestronglyMeasurable)
        hdψ ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans hsub)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select one positive local smoothing on each compact partition core,
with prescribed weighted derivative error in both coordinate directions. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_partition_smooth_approximants
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ, ∀j,
      (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
        ∀x, v j x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ (v j) x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v j x - u x))
        2 volume < ε j) := by
  classical
  suffices H : ∀j, ∃v : EuclideanPlane → ℝ,
      (ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧ ∀x, v x ∈ Icc 0 1) ∧
      (∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
        ∀x ∈ tsupport (ρ.weight j), v x ∈ Icc a b) ∧
      (∀i : Fin 2, eLpNorm (fun x =>
        ρ.weight j x * ((fderiv ℝ v x) (EuclideanSpace.single i 1) -
          (hu j).weakGrad x i) +
        (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (v x - u x))
        2 volume < ε j) by
    choose v hv using H
    exact ⟨v, hv⟩
  intro j
  obtain ⟨V, φ, hV, hKV, hVW, hsmooth, _, hvalue, hgrad, _, hinterval⟩ :=
    exists_local_positive_sobolev_smoothing (hW j) (ρ.compact j).isCompact
      (hsub j) (hu j) (hunit j)
  let hw := (hu j).restrict hV hVW
  have hgrad' (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 (volume.restrict V)) atTop (𝓝 0) := by
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using hgrad i
  have herr (i : Fin 2) := tendsto_partition_derivative_error hV hw
    (fun n => (hsmooth n).1) hvalue hgrad' (ρ.smooth j) (ρ.compact j) hKV i
  have he : ∀ᶠ n in atTop, ∀i : Fin 2, eLpNorm (fun x =>
      ρ.weight j x * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
        (hu j).weakGrad x i) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * (φ n x - u x))
      2 volume < ε j := by
    apply eventually_all.mpr
    intro i
    simpa only [hw, DeGiorgi.MemW1pWitness.restrict] using
      (tendsto_order.1 (herr i)).2 (ε j) (hε j)
  obtain ⟨n, hn, hb⟩ := (he.and hinterval).exists
  exact ⟨φ n, hsmooth n, hb, hn⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionMixing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth mixing on an open planar domain. The locally finite sum is
represented by an actual finite sum in a neighborhood of each point. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem point_finite (x : EuclideanPlane) : HasFiniteSupport (fun i => ρ.weight i x) := by
  by_cases hx : x ∈ Ω
  · exact ρ.locallyFinite.point_finite ⟨x, hx⟩
  · have hz : ∀i, ρ.weight i x = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (ρ.inside i h))
    change (Function.support (fun i => ρ.weight i x)).Finite
    apply finite_empty.subset
    intro i hi
    exact False.elim (hi (hz i))

theorem mix_mem_Icc (v : ι → EuclideanPlane → ℝ) {x : EuclideanPlane}
    (hx : x ∈ Ω) {a b : ℝ} (hv : ∀i, ρ.weight i x ≠ 0 → v i x ∈ Icc a b) :
    ρ.mix v x ∈ Icc a b := by
  simpa only [mix, smul_eq_mul] using (convex_Icc a b).finsum_mem
    (fun i => ρ.nonneg i x) (ρ.sum_one ⟨x, hx⟩) hv

theorem eventually_finite_weights {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ∀ᶠ y in 𝓝 x, ∀i ∉ s, ρ.weight i y = 0 := by
  classical
  obtain ⟨T, hT, hfin⟩ := ρ.locallyFinite ⟨x, hx⟩
  refine ⟨hfin.toFinset, ?_⟩
  have hsub : ∀ᶠ y : Ω in 𝓝 ⟨x, hx⟩, ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := by
    filter_upwards [hT] with y hy i hi
    by_contra hn
    apply hi
    exact hfin.mem_toFinset.mpr ⟨y, hn, hy⟩
  have hmap : ∀ᶠ y in Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 ⟨x, hx⟩),
      ∀i ∉ hfin.toFinset, ρ.weight i y = 0 := hsub
  have hm : Filter.map (Subtype.val : Ω → EuclideanPlane) (𝓝 (⟨x, hx⟩ : Ω)) = 𝓝 x :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨x, hx⟩
  rwa [hm] at hmap

theorem mix_eventually_eq_sum (v : ι → EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι, ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  refine ⟨s, hs.mono fun y hy => ?_⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change ρ.weight i y * v i y = 0
  rw [hy i his, zero_mul]

theorem mix_contDiffOn (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ρ.mix v) Ω := by
  intro x hx
  obtain ⟨s, hs⟩ := ρ.mix_eventually_eq_sum v hx
  apply ContDiffAt.contDiffWithinAt
  apply ((ContDiff.sum (fun i _ => (ρ.smooth i).mul (hv i))).contDiffAt).congr_of_eventuallyEq
  exact hs

theorem mix_fderiv (v : ι → EuclideanPlane → ℝ)
    (hv : ∀i, ContDiff ℝ (⊤ : ℕ∞) (v i)) {x : EuclideanPlane} (hx : x ∈ Ω) :
    fderiv ℝ (ρ.mix v) x =
      ∑ᶠ i, fderiv ℝ (fun y => ρ.weight i y * v i y) x := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have hsum : ρ.mix v =ᶠ[𝓝 x] fun y => ∑ i ∈ s, ρ.weight i y * v i y := by
    filter_upwards [hs] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    by_contra his
    apply hi
    change ρ.weight i y * v i y = 0
    rw [hy i his, zero_mul]
  rw [hsum.fderiv_eq]
  rw [fderiv_fun_sum (fun i _ =>
    ((ρ.smooth i).mul (hv i)).differentiable (by simp) x)]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra his
  apply hi
  change fderiv ℝ (fun y => ρ.weight i y * v i y) x = 0
  have hz : (fun y => ρ.weight i y * v i y) =ᶠ[𝓝 x] (fun _ => 0) :=
    hs.mono fun y hy => by
      change ρ.weight i y * v i y = 0
      rw [hy i his, zero_mul]
  rw [hz.fderiv_eq]
  exact fderiv_const_apply 0

end OpenPlanePartition

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionErrorSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected local smoothing errors have a globally controlled L²
sum. Finiteness at each point follows from local finiteness of the weights. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partitionDerivativeError_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (u : EuclideanPlane → ℝ)
    (G : ι → EuclideanPlane → EuclideanPlane) (v : ι → EuclideanPlane → ℝ)
    (i : Fin 2) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => partitionDerivativeError ρ u G v i j x) := by
  classical
  by_cases hx : x ∈ Ω
  · obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
    apply s.finite_toSet.subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hjs
    have hd : fderiv ℝ (ρ.weight j) x = 0 := by
      rw [hz.fderiv_eq]
      exact fderiv_const_apply 0
    simp only [partitionDerivativeError, hz.eq_of_nhds, hd,
      zero_apply, zero_mul, zero_add]
  · apply finite_empty.subset
    intro j hj
    apply False.elim
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    have hnot : x ∉ tsupport (ρ.weight j) := fun h => hx (ρ.inside j h)
    simp only [partitionDerivativeError, image_eq_zero_of_notMem_tsupport hnot,
      fderiv_of_notMem_tsupport ℝ hnot, zero_apply, zero_mul, zero_add]

theorem exists_partition_approximation_with_summed_error
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : ι → EuclideanPlane → ℝ,
      (∀j, (ContDiff ℝ (⊤ : ℕ∞) (v j) ∧ HasCompactSupport (v j) ∧
          ∀x, v j x ∈ Icc 0 1) ∧
        ∀a b : ℝ, (∀x ∈ W j, u x ∈ Icc a b) →
          ∀x ∈ tsupport (ρ.weight j), v j x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x => ∑ᶠ j,
        partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
        2 volume ≤ ∑' j, ε j := by
  obtain ⟨v, hv⟩ := exists_partition_smooth_approximants ρ W hW hsub u hu hunit ε hε
  refine ⟨v, fun j => ⟨(hv j).1, (hv j).2.1⟩, ?_⟩
  intro i
  apply (eLpNorm_finsum_le_tsum_of_pointFinite volume _ ?_
    (partitionDerivativeError_pointFinite ρ u _ v i)).trans
  · exact ENNReal.tsum_le_tsum (fun j => ((hv j).2.2 i).le)
  · intro j
    exact aestronglyMeasurable_partition_derivative_error (hW j) (hu j)
      (hv j).1.1 (ρ.smooth j) (hsub j) i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientIdentity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total selected error is the derivative of the smooth partition
sum minus the corresponding partition of local weak gradients. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity
namespace OpenPlanePartition

variable {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
  (ρ : OpenPlanePartition Ω ι)

theorem finite_weights_and_derivatives {x : EuclideanPlane} (hx : x ∈ Ω) :
    ∃s : Finset ι,
      (∀j ∉ s, ρ.weight j x = 0 ∧ fderiv ℝ (ρ.weight j) x = 0) ∧
      (ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y) ∧
      (∑j ∈ s, ρ.weight j x) = 1 ∧ (∑j ∈ s, fderiv ℝ (ρ.weight j) x) = 0 := by
  classical
  obtain ⟨s, hs⟩ := ρ.eventually_finite_weights hx
  have heq : ρ.mix (fun _ _ => 1) =ᶠ[𝓝 x] fun y => ∑j ∈ s, ρ.weight j y := by
    filter_upwards [hs] with y hy
    simp only [mix, mul_one]
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  have hone : (fun y => ∑j ∈ s, ρ.weight j y) =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hs, Ω.isOpen.mem_nhds hx] with y hy hyΩ
    rw [← ρ.sum_one ⟨y, hyΩ⟩]
    symm
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hy j hjs)
  refine ⟨s, ?_, heq, hone.eq_of_nhds, ?_⟩
  · intro j hj
    have hz : ρ.weight j =ᶠ[𝓝 x] (fun _ => 0) := hs.mono fun _ hy => hy j hj
    refine ⟨hz.eq_of_nhds, ?_⟩
    rw [hz.fderiv_eq]
    exact fderiv_const_apply 0
  · calc
      _ = fderiv ℝ (fun y => ∑j ∈ s, ρ.weight j y) x :=
        (fderiv_fun_sum (fun j _ => (ρ.smooth j).differentiable (by simp) x)).symm
      _ = fderiv ℝ (fun _ : EuclideanPlane => (1 : ℝ)) x := hone.fderiv_eq
      _ = 0 := fderiv_const_apply 1

theorem mix_gradient_error_identity
    (u : EuclideanPlane → ℝ) (G : ι → EuclideanPlane → EuclideanPlane)
    (v : ι → EuclideanPlane → ℝ) (hv : ∀j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    {x : EuclideanPlane} (hx : x ∈ Ω) (i : Fin 2) :
    (fderiv ℝ (ρ.mix v) x) (EuclideanSpace.single i 1) -
      (∑ᶠ j, ρ.weight j x * G j x i) =
      ∑ᶠ j, partitionDerivativeError ρ u G v i j x := by
  classical
  obtain ⟨s, hz, _, _, hd⟩ := ρ.finite_weights_and_derivatives hx
  have hmix := ρ.mix_fderiv v hv hx
  have hzero (j : ι) (hj : j ∉ s) :
      fderiv ℝ (fun y => ρ.weight j y * v j y) x = 0 := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x), (hz j hj).1, (hz j hj).2]
    simp
  have hf : (∑ᶠ j, fderiv ℝ (fun y => ρ.weight j y * v j y) x) =
      ∑j ∈ s, fderiv ℝ (fun y => ρ.weight j y * v j y) x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    exact hj (hzero j hjs)
  have hG : (∑ᶠ j, ρ.weight j x * G j x i) = ∑j ∈ s, ρ.weight j x * G j x i := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change ρ.weight j x * G j x i = 0
    rw [(hz j hjs).1, zero_mul]
  have herr : (∑ᶠ j, partitionDerivativeError ρ u G v i j x) =
      ∑j ∈ s, partitionDerivativeError ρ u G v i j x := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change partitionDerivativeError ρ u G v i j x = 0
    simp only [partitionDerivativeError, (hz j hjs).1, (hz j hjs).2,
      zero_apply, zero_mul, zero_add]
  have hd' : (∑j ∈ s, (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [sum_apply, zero_apply] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hd
  rw [hmix, hf, hG, herr]
  simp only [sum_apply]
  have hprod (j : ι) :
      (fderiv ℝ (fun y => ρ.weight j y * v j y) x) (EuclideanSpace.single i 1) =
      ρ.weight j x * (fderiv ℝ (v j) x) (EuclideanSpace.single i 1) +
      (fderiv ℝ (ρ.weight j) x) (EuclideanSpace.single i 1) * v j x := by
    rw [fderiv_fun_mul ((ρ.smooth j).differentiable (by simp) x)
      ((hv j).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod, partitionDerivativeError, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hd']
  ring

end OpenPlanePartition
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PositivePartitionSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing on an open plane domain with a prescribed sum of
local gradient errors. All approximants and partition weights are constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_positive_partition_smoothing
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, IsOpen (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (u : EuclideanPlane → ℝ) (hu : ∀j, DeGiorgi.MemW1pWitness 2 u (W j))
    (hunit : ∀j x, x ∈ W j → u x ∈ Icc 0 1)
    (ε : ι → ℝ≥0∞) (hε : ∀j, 0 < ε j) :
    ∃v : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀x ∈ Ω, v x ∈ Icc 0 1) ∧
      (∀x ∈ Ω, ∀a b : ℝ,
        (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, u y ∈ Icc a b) → v x ∈ Icc a b) ∧
      ∀i : Fin 2, eLpNorm (fun x =>
        (fderiv ℝ v x) (EuclideanSpace.single i 1) -
          ∑ᶠ j, ρ.weight j x * (hu j).weakGrad x i) 2 (volume.restrict Ω) ≤ ∑' j, ε j := by
  obtain ⟨v, hv, he⟩ := exists_partition_approximation_with_summed_error
    ρ W hW hsub u hu hunit ε hε
  have hsmooth (j : ι) := (hv j).1.1
  refine ⟨ρ.mix v, ρ.mix_contDiffOn v hsmooth, ?_, ?_, ?_⟩
  · intro x hx
    exact ρ.mix_mem_Icc v hx (fun j _ => (hv j).1.2.2 x)
  · intro x hx a b hab
    exact ρ.mix_mem_Icc v hx (fun j hj =>
      (hv j).2 a b (hab j hj) x (subset_tsupport (ρ.weight j) hj))
  · intro i
    calc
      _ = eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x)
          2 (volume.restrict Ω) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
        exact ρ.mix_gradient_error_identity u _ v hsmooth hx i
      _ ≤ eLpNorm (fun x => ∑ᶠ j,
          partitionDerivativeError ρ u (fun j => (hu j).weakGrad) v i j x) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ _ := he i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive partition preserves a common pointwise bound on local
weak-gradient components, and hence their common L² bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem partition_component_pointFinite
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (G : ι → EuclideanPlane → ℝ) (x : EuclideanPlane) :
    HasFiniteSupport (fun j => ρ.weight j x * G j x) := by
  apply (ρ.point_finite x).subset
  intro j hj
  by_contra hn
  apply hj
  change ρ.weight j x * G j x = 0
  rw [show ρ.weight j x = 0 from not_not.mp hn, zero_mul]

theorem partition_component_aestronglyMeasurable
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hG : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j))) :
    AEStronglyMeasurable (fun x => ∑ᶠ j, ρ.weight j x * G j x) volume := by
  exact aestronglyMeasurable_finsum_of_pointFinite volume _
    (fun j => aestronglyMeasurable_mul_of_support (hW j) (hG j) (ρ.smooth j).continuous
      ((subset_tsupport (ρ.weight j)).trans (hsub j)))
    (partition_component_pointFinite ρ G)

theorem partition_component_bound
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ) (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    ∀ᵐ x ∂volume.restrict Ω, |∑ᶠ j, ρ.weight j x * G j x| ≤ g x := by
  have hglobal : ∀ᵐ x ∂(volume : Measure EuclideanPlane), ∀j, x ∈ W j → |G j x| ≤ g x :=
    ae_all_iff.mpr (fun j => (ae_restrict_iff' (hW j)).1 (hG j))
  filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  have hb : (∑ᶠ j, ρ.weight j x * G j x) ∈ Icc (-g x) (g x) := by
    simpa only [smul_eq_mul] using (convex_Icc (-g x) (g x)).finsum_mem
      (fun j => ρ.nonneg j x) (ρ.sum_one ⟨x, hxΩ⟩)
      (fun j hj => abs_le.mp (hx j (hsub j (subset_tsupport (ρ.weight j) hj))))
  exact abs_le.mpr hb

theorem partition_component_memLp
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x) :
    MemLp (fun x => ∑ᶠ j, ρ.weight j x * G j x) 2 (volume.restrict Ω) := by
  apply hg.of_le (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).restrict
  filter_upwards [partition_component_bound ρ W hW hsub G g hG] with x hx
  simpa only [Real.norm_eq_abs] using hx.trans (le_abs_self (g x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionGradientEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the constructed gradient error and a common local density bound
into a global finite-energy estimate for the actual smooth function. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem partition_smooth_gradient_energy
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    {g : EuclideanPlane → ℝ} (hg : MemLp g 2 (volume.restrict Ω))
    (hG : ∀j, ∀ᵐ x ∂volume.restrict (W j), |G j x| ≤ g x)
    {w : EuclideanPlane → ℝ}
    (i : Fin 2) {ε : ℝ≥0∞}
    (herr : eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1) -
      ∑ᶠj, ρ.weight j x * G j x) 2 (volume.restrict Ω) < ε) :
    MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
    eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
      ε + eLpNorm g 2 (volume.restrict Ω) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠj, ρ.weight j x * G j x
  let D : EuclideanPlane → ℝ := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)
  have hP : MemLp P 2 (volume.restrict Ω) :=
    partition_component_memLp ρ W hW hsub G hGm hg hG
  have hE : MemLp (fun x => D x - P x) 2 (volume.restrict Ω) :=
    ⟨(measurable_fderiv_apply_const ℝ w _).aestronglyMeasurable.sub hP.1, herr.trans_le le_top⟩
  have hsum : (fun x => (D x - P x) + P x) = D := by
    funext x
    exact sub_add_cancel _ _
  have hnormP : eLpNorm P 2 (volume.restrict Ω) ≤ eLpNorm g 2 (volume.restrict Ω) := by
    apply eLpNorm_mono_ae_real
    simpa only [Real.norm_eq_abs] using partition_component_bound ρ W hW hsub G g hG
  constructor
  · have hh := hE.add hP
    change MemLp D 2 (volume.restrict Ω)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact (sub_add_cancel (D x) (P x)).symm
  · change eLpNorm D 2 (volume.restrict Ω) ≤ _
    calc
      _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict Ω) := by rw [hsum]
      _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict Ω) +
          eLpNorm P 2 (volume.restrict Ω) := eLpNorm_add_le hE.1 hP.1 (by norm_num)
      _ ≤ _ := add_le_add herr.le hnormP

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OpenDomainRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A globally measurable representative of a smooth function on an open
physical plane domain, preserving its actual derivatives there. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem openZeroExtension_eq {D : Set EuclideanPlane} {w : EuclideanPlane → ℝ}
    {x : EuclideanPlane} (hx : x ∈ D) : openZeroExtension D w x = w x := by
  classical
  exact piecewise_eq_of_mem D w (fun _ => 0) hx

theorem openZeroExtension_measurable {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} (hw : ContinuousOn w D) : Measurable (openZeroExtension D w) := by
  classical
  exact hw.measurable_piecewise continuousOn_const hD.measurableSet

theorem openZeroExtension_contDiffOn {D : Set EuclideanPlane}
    {w : EuclideanPlane → ℝ} (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D) :
    ContDiffOn ℝ (⊤ : ℕ∞) (openZeroExtension D w) D :=
  hw.congr (fun _ hx => openZeroExtension_eq hx)

theorem openZeroExtension_fderiv {D : Set EuclideanPlane} (hD : IsOpen D)
    (w : EuclideanPlane → ℝ) {x : EuclideanPlane} (hx : x ∈ D) :
    fderiv ℝ (openZeroExtension D w) x = fderiv ℝ w x := by
  have he : openZeroExtension D w =ᶠ[𝓝 x] w := by
    filter_upwards [hD.mem_nhds hx] with y hy
    exact openZeroExtension_eq hy
  exact he.fderiv_eq

theorem openZeroExtension_gradient_memLp {D : Set EuclideanPlane} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ} {i : Fin 2}
    (hw : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict D)) :
    MemLp (fun x => (fderiv ℝ (openZeroExtension D w) x) (EuclideanSpace.single i 1))
      2 (volume.restrict D) := by
  apply hw.ae_eq
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  rw [openZeroExtension_fderiv hD w hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RealGradientNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact L² preservation for each derivative component under the planar
coordinate change used by finite transfer. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_chart_zeroExtension_partial_eLpNorm {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D))) :
    eLpNorm (fun p =>
        (fderiv ℝ ((openZeroExtension (euclideanPlaneCoordinates ⁻¹' D) w) ∘
          euclideanPlaneCoordinates.symm) p) (if i = 0 then (1, 0) else (0, 1)))
        2 (volume.restrict D) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) := by
  have hΩ := hD.preimage euclideanPlaneCoordinates.continuous
  rw [real_chart_partial_eLpNorm hD (openZeroExtension_contDiffOn hw) i
    (openZeroExtension_gradient_memLp hΩ hi)]
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [openZeroExtension_fderiv hΩ w hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_open_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' U) = U := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    let K : Set X := π ⁻¹' {π p}
    have hpK : p ∈ K := rfl
    have hmiss : Disjoint K (frontier U) := by
      apply Set.disjoint_left.mpr
      intro z hz hzfront
      have hpz : p = z := hsing z hzfront p hz.symm
      have hpfront : p ∈ frontier U := hpz.symm ▸ hzfront
      rw [hU.frontier_eq] at hpfront
      exact hpfront.2 hp
    have hsplit : K ⊆ U ∨ K ⊆ (closure U)ᶜ := by
      apply (hfibers (π p)).subset_or_subset hU isClosed_closure.isOpen_compl
      · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
      · intro z hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · right
          intro hzcl
          apply Set.disjoint_left.mp hmiss hz
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
    rcases hsplit with hin | hout
    · exact hin hpq.symm
    · exact (hout hpK (subset_closure hp)).elim
  · exact subset_preimage_image π U

/-- Physical Jordan disks with boundary in the domain are saturated for
the actual component-collapse quotient. -/
theorem preimage_image_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
  apply preimage_image_open_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

/-- The saturated physical disk projects to an open quotient neighborhood. -/
theorem isOpen_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsOpen (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  apply (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary]
  exact OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SliceMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability from almost-everywhere continuous horizontal sections
and measurable vertical sections on a dense set. Finite simple sampling
provides the measurable approximants. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {A B : Type*} [MetricSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A] [Nonempty A] [MeasurableSpace B]

theorem aestronglyMeasurable_of_dense_measurable_slices
    (μ : Measure A) (ν : Measure B) [SFinite ν] (f : A × B → ℝ)
    (D : Set A) (hD : Dense D)
    (hvertical : ∀x ∈ D, Measurable fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hD.nonempty
  let q (n : ℕ) : SimpleFunc A A := SimpleFunc.approxOn id measurable_id D x₀ hx₀ n
  have hq (n : ℕ) (x : A) : q n x ∈ D := SimpleFunc.approxOn_mem measurable_id hx₀ n x
  let F (n : ℕ) (p : A × B) := f (q n p.1, p.2)
  have hF (n : ℕ) : Measurable (F n) := by
    let Q := {x : A // x ∈ (q n).range}
    let q' : A → Q := fun x => ⟨q n x, (q n).mem_range_self x⟩
    have hq' : Measurable q' := (q n).measurable.subtype_mk
    have hv : Measurable (fun p : Q × B => f (p.1.val, p.2)) := by
      apply measurable_from_prod_countable_right
      intro x
      apply hvertical x.val
      obtain ⟨a, ha⟩ := SimpleFunc.mem_range.mp x.property
      exact ha ▸ hq n a
    exact hv.comp ((hq'.comp measurable_fst).prodMk measurable_snd)
  apply aestronglyMeasurable_of_tendsto_ae (f := F) atTop
    (fun n => (hF n).stronglyMeasurable.aestronglyMeasurable)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hhorizontal] with p hp
  exact hp.tendsto p.1 |>.comp (SimpleFunc.tendsto_approxOn measurable_id hx₀ (hD p.1))

theorem aestronglyMeasurable_of_ae_continuous_slices
    [TopologicalSpace B] [BorelSpace B]
    (μ : Measure A) [μ.IsOpenPosMeasure] (ν : Measure B) [SFinite ν]
    (f : A × B → ℝ)
    (hvertical : ∀ᵐ x ∂μ, Continuous fun y => f (x, y))
    (hhorizontal : ∀ᵐ y ∂ν, Continuous fun x => f (x, y)) :
    AEStronglyMeasurable f (μ.prod ν) := by
  apply aestronglyMeasurable_of_dense_measurable_slices μ ν f
    {x | Continuous fun y => f (x, y)} (μ.dense_of_ae hvertical)
  · intro x hx
    exact hx.measurable
  · exact hhorizontal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IntegralLineAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A linewise integral bound yields actual absolute continuity, without
first choosing a measurable representative for the bounded potential. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem absolutelyContinuousOnInterval_of_dist_le
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  apply lt_of_le_of_lt _ (h E hE hlen)
  exact Finset.sum_le_sum fun i hi => hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

theorem absolutelyContinuousOnInterval_of_integral_bound
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      dist (f x) (f y) ≤ ∫t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  apply absolutelyContinuousOnInterval_of_dist_le
    (hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc))
  intro x hx y hy
  apply (hfg x hx y hy).trans
  rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hx)))
    (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc hy))),
    intervalIntegral.abs_intervalIntegral_eq]
  simpa only [uIoc_comm y x] using (le_abs_self (∫t in uIoc x y, g t))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectangleMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local ACL gives a measurable representative on the open rectangle.
This avoids any analyticity assumption on the finite-chain infimum. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem aestronglyMeasurable_on_rectangle_of_ACL
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hh : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hv : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
  let U := Ioo a b
  let V := Ioo c d
  let μ : Measure U := volume.comap ((↑) : U → ℝ)
  let ν : Measure V := volume.comap ((↑) : V → ℝ)
  obtain ⟨u, hau, hub⟩ := exists_between hab
  let : Nonempty U := ⟨⟨u, hau, hub⟩⟩
  let : μ.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hμuniv : μ univ = volume U := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  have hνuniv : ν univ = volume V := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioo).comap_apply]
    simp only [image_univ, Subtype.range_coe]
    rfl
  let : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact measure_Ioo_lt_top⟩
  let : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_Ioo_lt_top⟩
  have hhv : ∀ᵐ y ∂ν, Continuous fun x : U => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hh
    have h' : ∀ᵐ y : V ∂ν, AbsolutelyContinuousOnInterval (fun x => f (x, y.val)) a b :=
      (ae_restrict_iff_subtype (s := V) measurableSet_Ioo).mp h
    filter_upwards [h'] with y hy
    have hc : ContinuousOn (fun x => f (x, y.val)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using hy.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hvh : ∀ᵐ x ∂μ, Continuous fun y : V => f (x.val, y.val) := by
    have h := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hv
    have h' : ∀ᵐ x : U ∂μ, AbsolutelyContinuousOnInterval (fun y => f (x.val, y)) c d :=
      (ae_restrict_iff_subtype (s := U) measurableSet_Ioo).mp h
    filter_upwards [h'] with x hx
    have hc : ContinuousOn (fun y => f (x.val, y)) (Icc c d) := by
      simpa only [uIcc_of_le hcd.le] using hx.continuousOn
    exact (hc.mono Ioo_subset_Icc_self).domRestrict
  have hF : AEStronglyMeasurable (fun p : U × V => f (p.1.val, p.2.val)) (μ.prod ν) :=
    aestronglyMeasurable_of_ae_continuous_slices μ ν _ hvh hhv
  have hmap : (μ.prod ν).map (Prod.map ((↑) : U → ℝ) ((↑) : V → ℝ)) =
      volume.restrict (Ioo a b ×ˢ Ioo c d) := by
    rw [← Measure.map_prod_map μ ν measurable_subtype_coe measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_Ioo, map_comap_subtype_coe measurableSet_Ioo,
      Measure.prod_restrict]
    rfl
  rw [← hmap]
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Ioo).prodMap
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo)).aestronglyMeasurable_map_iff.mpr hF

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectangleNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact rectangles form a neighborhood basis inside a planar open
set; countably many of their interiors suffice to patch measurability. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

theorem exists_closed_rectangle_inside_open
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧ p ∈ Ioo a b ×ˢ Ioo c d ∧
      Icc a b ×ˢ Icc c d ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  refine ⟨p.1 - ε/2, p.1 + ε/2, p.2 - ε/2, p.2 + ε/2,
    by linarith, by linarith, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, ?_⟩
  intro q hq
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> apply abs_lt.mpr
  · constructor <;> linarith [hq.1.1, hq.1.2]
  · constructor <;> linarith [hq.2.1, hq.2.2]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ShrinkingRectangleCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate rectangles whose images have diameter controlled
by the distance to the dust. These are the sampling patches for smoothing. -/

open Set Metric

namespace CircleDomainRigidity

theorem dist_le_infDist_of_small_ball
    {X : Type*} [MetricSpace X] (B : Set X) {c x y : X}
    (hx : x ∈ ball c (infDist c B / 4)) (hy : y ∈ ball c (infDist c B / 4)) :
    dist y x ≤ infDist x B := by
  have hxc : dist c x < infDist c B / 4 := by simpa only [mem_ball, dist_comm] using hx
  have hyc : dist y c < infDist c B / 4 := hy
  have hi := infDist_le_infDist_add_dist (x := c) (y := x) (s := B)
  have ht := dist_triangle y c x
  linarith [infDist_nonneg (x := c) (s := B)]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmallShrinkingRectanglePartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking sampling rectangles with uniformly small physical diameter. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_closed_coordinate_rectangle_with_diameter
    {X : Type*} [MetricSpace X] {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty)
    {x : EuclideanPlane} (hx : x ∈ Ω) (hqx : q x ∉ B) :
    ∃a b c d : ℝ, a < b ∧ c < d ∧
      euclideanPlaneCoordinates x ∈ Ioo a b ×ˢ Ioo c d ∧
      (euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ Ω) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (q y) (q z) ≤ infDist (q z) B) ∧
      (∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        ∀z ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
          dist (⟨y 0, y 1⟩ : ℂ) (⟨z 0, z 1⟩ : ℂ) ≤ 1) := by
  let f : EuclideanPlane → ℂ := fun y => ⟨y 0, y 1⟩
  have hf : Continuous f :=
    Complex.equivRealProdCLM.symm.continuous.comp euclideanPlaneCoordinates.continuous
  let V := (Ω ∩ q ⁻¹' ball (q x) (infDist (q x) B / 4)) ∩ f ⁻¹' ball (f x) (1 / 2)
  have hδ : 0 < infDist (q x) B / 4 := div_pos
    ((hB.notMem_iff_infDist_pos hne).1 hqx) (by norm_num)
  have hV : IsOpen V := (hq.isOpen_inter_preimage hΩ isOpen_ball).inter (isOpen_ball.preimage hf)
  have hxV : x ∈ V := ⟨⟨hx, mem_ball_self hδ⟩, mem_ball_self (by norm_num)⟩
  have hVe : IsOpen (euclideanPlaneCoordinates '' V) :=
    euclideanPlaneCoordinates.toHomeomorph.isOpenMap V hV
  obtain ⟨a, b, c, d, hab, hcd, hpoint, hrect⟩ := exists_closed_rectangle_inside_open hVe
    (mem_image_of_mem euclideanPlaneCoordinates hxV)
  have hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, heq⟩ := hrect hy
    exact euclideanPlaneCoordinates.injective heq ▸ hz
  refine ⟨a, b, c, d, hab, hcd, hpoint, (hsub.trans inter_subset_left).trans inter_subset_left, ?_, ?_⟩
  · intro y hy z hz
    exact dist_le_infDist_of_small_ball B (hsub hz).1.2 (hsub hy).1.2
  · intro y hy z hz
    have h1 : dist (f y) (f x) < 1 / 2 := (hsub hy).2
    have h2' : dist (f z) (f x) < 1 / 2 := (hsub hz).2
    have h2 : dist (f x) (f z) < 1 / 2 := by simpa only [dist_comm] using h2'
    exact (dist_triangle (f y) (f x) (f z)).trans (by linarith)


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

theorem planar_energy_on_compact_finite {K : Set ℂ} (hK : IsCompact K)
    (g : ℂ → ℝ≥0∞)
    (henergy : (∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2) < ∞) :
    (∫⁻z in K, g z ^ 2) < ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_sphericalAreaDensity.continuousOn
  let c := ENNReal.ofReal (sphericalAreaDensity z₀)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z₀)).ne'
  have hcle (z : ℂ) (hz : z ∈ K) : c ≤ ENNReal.ofReal (sphericalAreaDensity z) :=
    ENNReal.ofReal_le_ofReal (hmin hz)
  have hbound : c * (∫⁻z in K, g z ^ 2) < ∞ := by
    rw [← lintegral_const_mul' c _ (by exact ENNReal.ofReal_ne_top)]
    apply lt_of_le_of_lt _ henergy
    calc
      (∫⁻z in K, c * g z ^ 2) ≤
          ∫⁻z in K, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 := by
        apply setLIntegral_mono' hK.measurableSet
        intro z hz
        exact mul_le_mul' (hcle z hz) le_rfl
      _ ≤ ∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  by_contra h
  have heq : (∫⁻z in K, g z ^ 2) = ∞ := top_unique (not_lt.mp h)
  simp [heq, ENNReal.mul_top hc] at hbound

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalDensityIntegrability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical quadratic energy supplies finite planar line density
on almost every horizontal and vertical line in each compact chart patch. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ 2 := by
  by_cases h : a ≤ 1
  · exact h.trans le_self_add
  · have ha : 1 ≤ a := le_of_not_ge h
    calc
      a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul' le_rfl ha
      _ ≤ 1 + a ^ 2 := by rw [pow_two]; exact le_add_self

theorem lintegral_lt_top_of_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ≥0∞)
    (hg : (∫⁻x, g x ^ 2 ∂μ) < ∞) : (∫⁻x, g x ∂μ) < ∞ := by
  apply lt_of_le_of_lt (lintegral_mono fun x => ennreal_le_one_add_sq (g x))
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
  exact ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ, hg⟩

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_2
theorem planar_density_on_compact_finite
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    {K : Set ℂ} (hK : IsCompact K) : (∫⁻z in K, g (z : Sphere)) < ∞ := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply lintegral_lt_top_of_sq
  apply planar_energy_on_compact_finite hK
  rwa [← lintegral_sphericalArea _ (hg.pow_const 2)]

theorem ae_finite_planar_density_slices
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    {K : Set ℂ} (hK : IsCompact K) :
    (∀ᵐ y : ℝ, (∫⁻x : ℝ, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩) < ∞) ∧
    (∀ᵐ x : ℝ, (∫⁻y : ℝ, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩) < ∞) := by
  let f : ℂ → ℝ≥0∞ := K.indicator (fun z => g (z : Sphere))
  have hf : Measurable f := (hg.comp OnePoint.continuous_coe.measurable).indicator hK.measurableSet
  have hfin : (∫⁻z, f z) < ∞ := by
    rw [lintegral_indicator hK.measurableSet]
    exact planar_density_on_compact_finite g hg henergy hK
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => f (Complex.equivRealProd.symm p)
  have hF : Measurable F := hf.comp Complex.measurableEquivRealProd.symm.measurable
  have hFfin : (∫⁻p, F p) < ∞ := by
    calc
      _ = ∫⁻z, f z :=
        (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hf
      _ < ∞ := hfin
  constructor
  · apply ae_lt_top hF.lintegral_prod_left'
    rw [← lintegral_prod_symm F hF.aemeasurable]
    exact hFfin.ne
  · apply ae_lt_top hF.lintegral_prod_right'
    rw [← lintegral_prod F hF.aemeasurable]
    exact hFfin.ne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LineLIntegralAbsoluteContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The line-integral criterion in extended nonnegative form. It applies
directly to the measurable path densities used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

open AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X]

theorem absolutelyContinuousOnInterval_of_lintegral_bound
    {f : ℝ → X} {g : ℝ → ℝ≥0∞} {a b : ℝ}
    (hg : (∫⁻t in uIoc a b, g t) < ∞)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  let S (E : ℕ × (ℕ → ℝ × ℝ)) := ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim : Tendsto (fun E => ∫⁻t in S E, g t ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero hg.ne (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero a b)
  have hr := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  simp only [ENNReal.toReal_zero] at hr
  apply squeeze_zero' (Eventually.of_forall fun E =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg)) _ hr
  have hev : ∀ᶠ E in totalLengthFilter ⊓ 𝓟 (disjWithin a b), E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hev] with E hE
  have hfin : (∫⁻t in S E, g t ∂volume.restrict (uIoc a b)) ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_mono_set (subset_univ (S E)))
      (by simpa only [Measure.restrict_univ] using hg)).ne
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)]
  change (∑i ∈ Finset.range E.1, ENNReal.ofReal (dist (f (E.2 i).1) (f (E.2 i).2))) ≤
    ∫⁻t in ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2,
      g t ∂volume.restrict (uIoc a b)
  rw [lintegral_biUnion_finset hE.2 (fun _ _ => measurableSet_uIoc)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Measure.restrict_restrict_of_subset
    (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzArclengthBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz parameterization has arclength measure dominated by
its Lipschitz constant times one-dimensional Hausdorff measure on time. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem lipschitz_pathLength_Icc_le (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Icc a b) ≤ L * edist b a := by
  rw [pathLengthMeasure_Icc γ hab]
  have h := hL.lipschitzOnWith.comp_eVariationOn_le (g := id) (s := Icc a b)
    (fun _ _ => mem_univ _)
  simpa only [Function.comp_id, variation_time_identity hab] using h

theorem lipschitz_pathLength_le_diameter (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (s : Set PathTime) :
    pathLengthMeasure γ s ≤ L * ediam s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : IsCompact (closure s) := isClosed_closure.isCompact
  obtain ⟨a, ha⟩ := hc.exists_isLeast hne.closure
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hne.closure
  have hab : a ≤ b := ha.2 hb.1
  have hs : s ⊆ Icc a b := fun t ht => ⟨ha.2 (subset_closure ht), hb.2 (subset_closure ht)⟩
  calc
    pathLengthMeasure γ s ≤ pathLengthMeasure γ (Icc a b) := measure_mono hs
    _ ≤ L * edist b a := lipschitz_pathLength_Icc_le γ hL hab
    _ ≤ L * ediam (closure s) := mul_le_mul' le_rfl (edist_le_ediam_of_mem hb.1 ha.1)
    _ = _ := by rw [ediam_closure]

theorem lipschitz_pathLength_le_hausdorff (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0) :
    pathLengthMeasure γ ≤ (L : ℝ≥0∞) • (μH[1] : Measure PathTime) := by
  have hL0' : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL0
  let μ : Measure PathTime := (L : ℝ≥0∞)⁻¹ • pathLengthMeasure γ
  have hμ : μ ≤ (μH[1] : Measure PathTime) := by
    apply Measure.le_hausdorffMeasure 1 μ ∞ (by simp)
    intro s _
    change (L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s ≤ ediam s ^ (1 : ℝ)
    rw [ENNReal.rpow_one]
    calc
      _ ≤ (L : ℝ≥0∞)⁻¹ * ((L : ℝ≥0∞) * ediam s) :=
        mul_le_mul' le_rfl (lipschitz_pathLength_le_diameter γ hL s)
      _ = ediam s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hL0' ENNReal.coe_ne_top, one_mul]
  apply Measure.le_iff.mpr
  intro s hs
  have h := mul_le_mul' (le_refl (L : ℝ≥0∞)) (hμ s)
  change (L : ℝ≥0∞) * ((L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s) ≤
    (L : ℝ≥0∞) * (μH[1] : Measure PathTime) s at h
  rwa [← mul_assoc, ENNReal.mul_inv_cancel hL0' ENNReal.coe_ne_top, one_mul] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BilipschitzPathCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted Hausdorff length pays for an actual embedded path
whenever the chosen parameter is Lipschitz in both directions. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bilipschitz_pathOccupation_le (γ : RectifiablePath X) {L K : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0)
    (hK : AntilipschitzWith K γ.val) :
    pathOccupation γ ≤ ((L : ℝ≥0∞) * K) •
      (μH[1] : Measure X).restrict (range γ.val) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [pathOccupation_apply γ hs]
  have he : γ.val ⁻¹' s = γ.val ⁻¹' (s ∩ range γ.val) := by
    ext t
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, mem_range_self t⟩, And.left⟩
  calc
    pathLengthMeasure γ (γ.val ⁻¹' s) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure PathTime) (γ.val ⁻¹' s) :=
      lipschitz_pathLength_le_hausdorff γ hL hL0 _
    _ = (L : ℝ≥0∞) * (μH[1] : Measure PathTime)
        (γ.val ⁻¹' (s ∩ range γ.val)) := by rw [he]
    _ ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * (μH[1] : Measure X) (s ∩ range γ.val)) := by
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.rpow_one] using
        hK.hausdorffMeasure_preimage_le (show (0 : ℝ) ≤ 1 by norm_num) (s ∩ range γ.val)
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, mul_assoc]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzIntervalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem realIntervalPath_antilipschitz {a b : ℝ} (hab : a ≠ b) :
    AntilipschitzWith (nndist a b)⁻¹ (realIntervalPath a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  change dist s t ≤ _ * dist (AffineMap.lineMap a b (s : ℝ))
    (AffineMap.lineMap a b (t : ℝ))
  rw [dist_lineMap_lineMap, Subtype.dist_eq, NNReal.coe_inv, coe_nndist,
    mul_left_comm, inv_mul_cancel₀ (dist_ne_zero.mpr hab), mul_one]

theorem range_realIntervalPath {a b : ℝ} (hab : a < b) :
    range (realIntervalPath a b) = Icc a b := by
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    exact realIntervalPath_mem hab.le s
  · intro y hy
    have hd : 0 < b - a := sub_pos.mpr hab
    let s : PathTime := ⟨(y-a)/(b-a), div_nonneg (sub_nonneg.mpr hy.1) hd.le,
      (div_le_one hd).mpr (sub_le_sub_right hy.2 a)⟩
    refine ⟨s, ?_⟩
    change AffineMap.lineMap a b ((y-a)/(b-a)) = y
    rw [AffineMap.lineMap_apply_module]
    dsimp
    field_simp
    ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzMappedArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz map multiplies actual path arclength by at most its
Lipschitz constant. The proof constructs the nonnegative Stieltjes difference. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pathLengthMeasure_le_of_interval_bounds
    (α : RectifiablePath X) (β : RectifiablePath Y) (L : ℝ≥0)
    (hI : ∀a b : PathTime, a ≤ b → pathLengthMeasure β (Icc a b) ≤
      (L : ℝ≥0∞) * pathLengthMeasure α (Icc a b)) :
    pathLengthMeasure β ≤ L • pathLengthMeasure α := by
  have hdiff (γ : RectifiablePath X) (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure γ (Icc a b) =
        ENNReal.ofReal (pathLengthFunction γ b - pathLengthFunction γ a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hdiffβ (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure β (Icc a b) =
        ENNReal.ofReal (pathLengthFunction β b - pathLengthFunction β a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure β)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hbound (a b : PathTime) (hab : a ≤ b) :
      pathLengthFunction β b - pathLengthFunction β a ≤
        L * (pathLengthFunction α b - pathLengthFunction α a) := by
    have h := hI a b hab
    rw [hdiff α a b hab, hdiffβ a b hab] at h
    have hnonneg : 0 ≤ (L : ℝ) * (pathLengthFunction α b - pathLengthFunction α a) :=
      mul_nonneg L.property (sub_nonneg.mpr ((pathLengthFunction α).mono hab))
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    rw [ENNReal.ofReal_mul (p := (L : ℝ))
      (q := pathLengthFunction α b - pathLengthFunction α a) L.property,
      ENNReal.ofReal_coe_nnreal]
    exact h
  let F : StieltjesFunction PathTime := {
    toFun := fun t => L * pathLengthFunction α t - pathLengthFunction β t
    mono' := by
      intro a b hab
      have h := hbound a b hab
      dsimp
      linarith
    right_continuous' := fun t =>
      (((continuous_pathLengthFunction α).const_mul (L : ℝ)).sub
        (continuous_pathLengthFunction β)).continuousAt.continuousWithinAt }
  have he : F + pathLengthFunction β = L • pathLengthFunction α := by
    apply StieltjesFunction.ext
    intro t
    change (L : ℝ) * pathLengthFunction α t - pathLengthFunction β t +
      pathLengthFunction β t = (L : ℝ) * pathLengthFunction α t
    ring
  have hmeasure := congrArg (fun f : StieltjesFunction PathTime => f.measure) he
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_smul] at hmeasure
  change F.measure + pathLengthMeasure β = L • pathLengthMeasure α at hmeasure
  rw [← hmeasure]
  exact le_add_of_nonneg_left bot_le

theorem lipschitzMappedPath_length_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S) :
    pathLengthMeasure (lipschitzMappedPath α f hL hα) ≤ L • pathLengthMeasure α := by
  apply pathLengthMeasure_le_of_interval_bounds
  intro a b hab
  rw [pathLengthMeasure_Icc _ hab, pathLengthMeasure_Icc _ hab]
  exact hL.comp_eVariationOn_le (fun t _ => hα t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzMappedCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical cost under a Lipschitz change of ambient metric. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem lipschitzMappedPath_cost_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂pathOccupation (lipschitzMappedPath α f hL hα)) ≤
      (L : ℝ≥0∞) * ∫⁻t, g (f (α.val t)) ∂pathLengthMeasure α := by
  rw [lintegral_pathOccupation _ hg]
  calc
    _ ≤ ∫⁻t, g (f (α.val t)) ∂(L • pathLengthMeasure α) :=
      lintegral_mono' (lipschitzMappedPath_length_le α f hL hα) (fun _ => le_rfl)
    _ = _ := by rw [lintegral_smul_measure]; rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_IntervalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted cost of a chart interval, bounded by the ordinary line
integral of the pulled-back density. Parameter speed cancels exactly. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

theorem realRectifiableInterval_occupation_le {a b : ℝ} (hab : a < b) :
    pathOccupation (realRectifiableInterval a b) ≤ volume.restrict (Icc a b) := by
  have h := bilipschitz_pathOccupation_le (realRectifiableInterval a b)
    (realIntervalPath_lipschitz a b) (by simpa only [ne_eq, nndist_eq_zero] using hab.ne)
    (realIntervalPath_antilipschitz hab.ne)
  have hne : nndist a b ≠ 0 := by
    simpa only [ne_eq, nndist_eq_zero] using hab.ne
  have hc : (nndist a b : ℝ≥0∞) * ↑((nndist a b)⁻¹) = 1 := by
    rw [← ENNReal.coe_mul, mul_inv_cancel₀ hne, ENNReal.coe_one]
  rw [hc, one_smul] at h
  simpa only [realRectifiableInterval, range_realIntervalPath hab,
    hausdorffMeasure_real] using h

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem intervalChartPath_cost_le
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂pathOccupation (intervalChartPath φ hab.le hL)) ≤
      (L : ℝ≥0∞) * ∫⁻t in Icc a b, g (φ t) := by
  let α := realRectifiableInterval a b
  have hα : ∀t, α.val t ∈ Icc a b := fun t => realIntervalPath_mem hab.le t
  have hcost := lipschitzMappedPath_cost_le α φ hL hα g hg
  change (∫⁻y, g y ∂pathOccupation (intervalChartPath φ hab.le hL)) ≤ _ at hcost
  apply hcost.trans
  apply mul_le_mul' le_rfl
  calc
    _ = ∫⁻t, g (φ t) ∂pathOccupation α := (lintegral_pathOccupation α (hg.comp hφ)).symm
    _ ≤ _ := lintegral_mono' (realRectifiableInterval_occupation_le hab) fun _ => le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPathAdmissibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every path of finite physical length which stays off the dust is
allowed with inactive tags, for every residual measure and tuple exclusion. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem residualTimes_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualTimes B Γ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact h t ht.1

theorem residualImage_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualImage B Γ = ∅ := by
  rw [residualImage, residualTimes_empty_of_avoids h, image_empty]

theorem residualIncidence_empty_of_avoids {Z : Type*} [TopologicalSpace Z]
    {B : Set X} {Γ : TaggedPath X} (h : ∀ t, Γ.1 t ∉ B)
    (I : Set PathTime) (R : Set (Z × X)) (P : Set X) :
    {z | (Γ, z) ∈ residualIncidence B I R P} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨t, ht, _⟩
  rw [residualTimes_empty_of_avoids h] at ht
  exact ht

theorem residualConstraintFamily_of_avoids {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞) :
    ResidualConstraintFamily B R P ν m Γ := by
  intro i n a b
  unfold ResidualIncidenceBound
  rw [residualIncidence_empty_of_avoids h, measure_empty]
  exact bot_le

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_of_avoids (d : PathCodeData X Y)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (havoid : ∀ t, γ t ∉ d.dust) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) := by
  refine ⟨hfin, ?_, ?_, ?_, ?_⟩
  · intro k
    exact inactiveTag_rules d.levels N γ
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · rw [residualImage_empty_of_avoids havoid, measure_empty]

theorem domainPath_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (hγ : ∀ t, γ t ∈ d.quotientDomain) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) :=
  allowedTaggedPath_of_avoids d ν N γ hfin
    (fun t ht => Set.disjoint_left.mp hdisj (hγ t) ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rectifiable physical path entirely in the original domain projects
to an allowed quotient path, with exactly its original physical length. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

variable [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem projected_physical_path_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ d.physicalDomain) :
    AllowedTaggedPath d ν N (projectDomainPath d.domainEquiv β.val hβ, fun _ => inactiveTag) := by
  apply domainPath_allowed d hdisj ν N _ _ (projectDomainPath_mem d.domainEquiv β.val hβ)
  rw [physicalDomainLength_project]
  exact lt_top_iff_ne_top.mpr β.property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DomainPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a path contained in the physical domain, the dyadic occupation
kernel is exactly ordinary arclength occupation, with multiplicity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalStageOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) = pathOccupation β := by
  have he (i : Fin (2 ^ n)) :
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i (projectDomainPath e β.val hβ)) =
        pathPortionOccupation β (dyadicLeft n i) (dyadicRight n i) := by
    rw [physicalDyadicPath_project]
    change rectifiableOccupationCode (clippedPath β (dyadicLeft_le_right n i)).val = _
    rw [rectifiableOccupationCode_eq (clippedPath β (dyadicLeft_le_right n i)).property]
    exact pathOccupation_clipped β (dyadicLeft_le_right n i)
  ext E hE
  have hsum := congrArg (fun ν : Measure PathTime => ν (β.val ⁻¹' E))
    (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at hsum
  simpa only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply, he,
    pathPortionOccupation, Measure.map_apply β.val.continuous.measurable hE,
    pathOccupation_apply β hE] using hsum

theorem dyadicPhysicalOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    dyadicPhysicalOccupation e y₀ (finiteProjectedPhysicalPath e y₀ β hβ) = pathOccupation β := by
  ext E hE
  rw [dyadicPhysicalOccupation_apply e y₀ _ hE]
  change (⨆ n, physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) E) = _
  simp only [physicalStageOccupation_project, iSup_const]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NarrowedTagRules
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Narrowing a tag changes only its time interval. Every retained tag has
the original level tuple and continues to obey the level and null-set rules. -/

open Set
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem active_mem_tagTupleExcluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (q : TagData) : (Sum.inr q : TagSlot) ∈ tagTupleExcluded N ↔ q.2.2.1 ∈ N q.1 q.2.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨l, p, hp, he⟩ := mem_iUnion.mp hn
    have hq : (⟨n, l, p⟩ : TagData) = q := Sum.inr.inj he
    cases hq
    exact hp.1
  · intro h
    exact mem_iUnion.mpr ⟨q.1, mem_iUnion.mpr ⟨q.2.1, q.2.2, ⟨h, mem_univ _⟩, rfl⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PotentialPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed potential controls every physical domain path. In
particular it controls ordinary chart segments with their line density. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_physical_path_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (β : RectifiablePath Y) (hβ : ∀t, β.val t ∈ d.physicalDomain) :
    ENNReal.ofReal |u (d.domainEquiv ⟨β.val ⊤, hβ ⊤⟩).val -
      u (d.domainEquiv ⟨β.val ⊥, hβ ⊥⟩).val| ≤ 4 * ∫⁻y, g y ∂pathOccupation β := by
  let γ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint β hβ
  let Γ : TaggedPhysicalPath d := (γ, fun _ => inactiveTag)
  have hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2) :=
    projected_physical_path_allowed d hdisj ν N β hβ
  have htoll : boundaryToll γ.val m = 0 := by
    have hz (t : PathTime) : m (γ.val t) = 0 :=
      hm _ (projectDomainPath_mem d.domainEquiv β.val hβ t)
    simp only [boundaryToll, hz, tsum_zero]
  have hi := hpath Γ hΓ (projectDomainPath_mem d.domainEquiv β.val hβ ⊥)
    (projectDomainPath_mem d.domainEquiv β.val hβ ⊤)
  change ENNReal.ofReal |u (d.domainEquiv ⟨β.val ⊤, hβ ⊤⟩).val -
      u (d.domainEquiv ⟨β.val ⊥, hβ ⊥⟩).val| ≤
    4 * ((∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) + boundaryToll γ.val m) at hi
  rwa [htoll, add_zero, dyadicPhysicalOccupation_project] at hi

theorem potential_chart_interval_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain) :
    ENNReal.ofReal |v (φ b) - v (φ a)| ≤
      4 * ((L : ℝ≥0∞) * ∫⁻t in Icc a b, g (φ t)) := by
  let β := intervalChartPath φ hab.le hL
  have hβ : ∀t, β.val t ∈ d.physicalDomain :=
    fun t => hdom (realIntervalPath_mem hab.le t)
  have hi := potential_physical_path_bound d hdisj ν N u g m hm hpath β hβ
  rw [← hv (β.val ⊤) (hβ ⊤), ← hv (β.val ⊥) (hβ ⊥)] at hi
  have hi' : ENNReal.ofReal |v (φ b) - v (φ a)| ≤
      4 * ∫⁻y, g y ∂pathOccupation β := by
    simpa only [β, intervalChartPath, ContinuousMap.coe_mk, Function.comp_apply,
      realIntervalPath_zero, realIntervalPath_one] using hi
  exact hi'.trans (mul_le_mul' le_rfl (intervalChartPath_cost_le φ hφ hab hL g hg))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialLineRegularity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On each physical chart line with finite density integral, the actual
barrier pullback is absolutely continuous. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_chart_absolutelyContinuousOnInterval
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain)
    (hfinite : (∫⁻t in Icc a b, g (φ t)) < ∞) :
    AbsolutelyContinuousOnInterval (v ∘ φ) a b := by
  let ρ : ℝ → ℝ≥0∞ := fun t => 4 * ((L : ℝ≥0∞) * g (φ t))
  have hfρ : (∫⁻t in uIoc a b, ρ t) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono_set (show uIoc a b ⊆ Icc a b from by
      rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self))
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)
  have hseg (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
      ENNReal.ofReal |v (φ y) - v (φ x)| ≤ ∫⁻t in uIoc x y, ρ t := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hi := potential_chart_interval_bound d hdisj ν N u g hg m hm hpath v hv
      φ hφ hxy (hL.mono hsub) (fun t ht => hdom (hsub ht))
    rw [uIoc_of_le hxy.le]
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    have he : (∫⁻t in Ioc x y, g (φ t)) = ∫⁻t in Icc x y, g (φ t) :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rwa [he]
  apply absolutelyContinuousOnInterval_of_lintegral_bound hfρ
  intro x hx y hy
  rw [uIcc_of_le hab] at hx hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hseg x y hx hy hxy
  · subst y
    simp only [dist_self, ENNReal.ofReal_zero]
    exact bot_le
  · simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
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


theorem finite_sphere_chart_lipschitz_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hd : Continuous (fun z => ‖fderiv ℝ F z‖₊) :=
    (hF.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).nnnorm
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hd.continuousOn
  have hLip : LipschitzOnWith L F (closedBall (0 : ℂ) R) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by simp)).differentiableAt)
      (fun z hz => hL ⟨z, hz, rfl⟩) (convex_closedBall _ _)
  refine ⟨L, ?_⟩
  intro z hz w hw
  apply hLip
  · simpa only [mem_closedBall, dist_zero_right] using (hKR z hz).le
  · simpa only [mem_closedBall, dist_zero_right] using (hKR w hw).le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialRectangleACL
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barrier pullback is absolutely continuous on almost every
horizontal and vertical segment in each compact physical chart rectangle. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem isCompact_closedComplexRectangle (a b c e : ℝ) :
    IsCompact (closedComplexRectangle a b c e) :=
  (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

theorem mk_mem_closedComplexRectangle {a b c e x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c e) :
    (⟨x, y⟩ : ℂ) ∈ closedComplexRectangle a b c e :=
  ⟨(x, y), ⟨hx, hy⟩, rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_3
theorem potential_rectangle_ACL
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain) :
    (∀ᵐ y ∂volume.restrict (Icc c e),
      AbsolutelyContinuousOnInterval (fun x => v ((⟨x, y⟩ : ℂ) : Sphere)) a b) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => v ((⟨x, y⟩ : ℂ) : Sphere)) c e) := by
  let K := closedComplexRectangle a b c e
  have hK : IsCompact K := isCompact_closedComplexRectangle a b c e
  obtain ⟨L, hL⟩ := finite_sphere_chart_lipschitz_on_compact hK
  obtain ⟨hh, hvv⟩ := ae_finite_planar_density_slices g hg henergy hK
  constructor
  · filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_Icc] with y hy hyI
    let φ : ℝ → Sphere := fun x => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨t, y⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc a b) := by
      intro x hx x' hx'
      have h := hL (mk_mem_closedComplexRectangle hx hyI) (mk_mem_closedComplexRectangle hx' hyI)
      simpa only [Complex.edist_of_im_eq (show (⟨x, y⟩ : ℂ).im = (⟨x', y⟩ : ℂ).im from rfl)] using h
    have hfin : (∫⁻x in Icc a b, g (φ x)) < ∞ := by
      have he : (∫⁻x in Icc a b, g (φ x)) =
          ∫⁻x in Icc a b, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hx hyI)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hy
    exact potential_chart_absolutelyContinuousOnInterval d hdisj ν N u g hg m hm hpath
      v hv φ hφ hab hLip (fun x hx => hrect _ (mk_mem_closedComplexRectangle hx hyI)) hfin
  · filter_upwards [ae_restrict_of_ae hvv, ae_restrict_mem measurableSet_Icc] with x hx hxI
    let φ : ℝ → Sphere := fun y => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨x, t⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc c e) := by
      intro y hy y' hy'
      have h := hL (mk_mem_closedComplexRectangle hxI hy) (mk_mem_closedComplexRectangle hxI hy')
      simpa only [Complex.edist_of_re_eq (show (⟨x, y⟩ : ℂ).re = (⟨x, y'⟩ : ℂ).re from rfl)] using h
    have hfin : (∫⁻y in Icc c e, g (φ y)) < ∞ := by
      have he : (∫⁻y in Icc c e, g (φ y)) =
          ∫⁻y in Icc c e, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro y hy
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hxI hy)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hx
    exact potential_chart_absolutelyContinuousOnInterval d hdisj ν N u g hg m hm hpath
      v hv φ hφ hce hLip (fun y hy => hrect _ (mk_mem_closedComplexRectangle hxI hy)) hfin

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

theorem physical_closed_rectangle_of_coordinate_subset
    {G : Set Sphere} {a b c d : ℝ}
    (hsub : euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) ⊆ physicalPlaneDomain G) :
    ∀z ∈ closedComplexRectangle a b c d, (z : Sphere) ∈ G := by
  rintro z ⟨p, hp, rfl⟩
  have h := hsub (show euclideanPlaneCoordinates.symm p ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp)
  change planeSphere (euclideanPlaneCoordinates.symm p) ∈ G at h
  simpa only [planeSphere, complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h

theorem complex_rectangle_diameter_of_coordinate_diameter {a b c d : ℝ}
    (hdiam : ∀x ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
      ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d),
        dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) :
    ∀x ∈ closedComplexRectangle a b c d,
      ∀y ∈ closedComplexRectangle a b c d, dist x y ≤ 1 := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  have hx : euclideanPlaneCoordinates.symm p ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hy : euclideanPlaneCoordinates.symm q ∈
      euclideanPlaneCoordinates ⁻¹' (Icc a b ×ˢ Icc c d) := by
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hq
  have h := hdiam _ hx _ hy
  change dist (complexPlaneCoordinates (euclideanPlaneCoordinates.symm p))
    (complexPlaneCoordinates (euclideanPlaneCoordinates.symm q)) ≤ 1 at h
  simpa only [complexPlaneCoordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneQuotientRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Descend a physical planar function through the actual domain homeomorphism. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem quotientPlaneRepresentative_on_domain
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (p : Sphere) (hp : p ∈ d.physicalDomain) :
    quotientPlaneRepresentative d w (d.domainEquiv ⟨p, hp⟩).val =
      sphereFromPlaneFunction w p := by
  simp only [quotientPlaneRepresentative, dite_eq_left (d.domainEquiv ⟨p, hp⟩).property]
  have he : (⟨(d.domainEquiv ⟨p, hp⟩).val, (d.domainEquiv ⟨p, hp⟩).property⟩ :
      d.quotientDomain) = d.domainEquiv ⟨p, hp⟩ := rfl
  rw [he, Homeomorph.symm_apply_apply]

theorem quotientPlaneRepresentative_plane
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain d.physicalDomain) :
    quotientPlaneRepresentative d w (π (planeSphere x)) = w x := by
  have hp : planeSphere x ∈ d.physicalDomain := hx
  rw [← he ⟨planeSphere x, hp⟩, quotientPlaneRepresentative_on_domain d w _ hp]
  change sphereFromPlaneFunction w (complexPlaneCoordinates x : Sphere) = w x
  rw [sphereFromPlaneFunction_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem quotient_finite_plane_covers
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val) :
    d.quotientDomain \ {π OnePoint.infty} ⊆ (π ∘ planeSphere) '' physicalPlaneDomain d.physicalDomain := by
  intro y hy
  let p : d.physicalDomain := d.domainEquiv.symm ⟨y, hy.1⟩
  have hπp : π p.val = y := by
    rw [← he p]
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨y, hy.1⟩)
  have hp : p.val ≠ OnePoint.infty := by
    intro hinf
    exact hy.2 (by simpa only [mem_singleton_iff, hinf] using hπp.symm)
  obtain ⟨x, hx⟩ := exists_planeSphere_eq hp
  refine ⟨x, ?_, ?_⟩
  · change planeSphere x ∈ d.physicalDomain
    rw [hx]
    exact p.property
  · change π (planeSphere x) = y
    rwa [hx]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealPhysicalRepresentative
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable, smooth finite-plane representative with the constructed
Sobolev energy and the actual quotient pullback identity. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem exists_real_physical_representative
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain))) :
    ∃v : (ℝ × ℝ) → ℝ,
      Measurable v ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (FiniteTransfer.realChartDomain d.physicalDomain) ∧
      MemLp (FiniteTransfer.planarGradient v) 2
        (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) ∧
      (∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ v p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain))) ∧
      ∀z : ℂ, (z : Sphere) ∈ d.physicalDomain →
        v (Complex.equivRealProdCLM z) = quotientPlaneRepresentative d w (π z) := by
  let Ω := physicalPlaneDomain d.physicalDomain
  let D := FiniteTransfer.realChartDomain d.physicalDomain
  have hΩ : IsOpen Ω := isOpen_physicalPlaneDomain hG
  have hD : IsOpen D := FiniteTransfer.isOpen_realChartDomain hG
  let w₀ := openZeroExtension Ω w
  let v : (ℝ × ℝ) → ℝ := w₀ ∘ euclideanPlaneCoordinates.symm
  have hmeas : Measurable w₀ := openZeroExtension_measurable hΩ hw.continuousOn
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) w₀ (euclideanPlaneCoordinates ⁻¹' D) :=
    openZeroExtension_contDiffOn hw
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) v D := by
    apply hs.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn
    intro p hp
    simpa only [mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hgrad : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w₀ x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' D)) :=
    fun i => openZeroExtension_gradient_memLp hΩ (henergy i)
  refine ⟨v, hmeas.comp euclideanPlaneCoordinates.symm.continuous.measurable, hsm,
    real_chart_gradient_memLp hD hs hgrad, ?_, ?_⟩
  · intro i
    exact real_chart_zeroExtension_partial_eLpNorm hD hw i (henergy i)
  intro z hz
  let x := euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z)
  have heq : planeSphere x = (z : Sphere) := by
    apply congrArg ((↑) : ℂ → Sphere)
    change Complex.equivRealProdCLM.symm
      (euclideanPlaneCoordinates (euclideanPlaneCoordinates.symm (Complex.equivRealProdCLM z))) = z
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hx : x ∈ Ω := by
    change planeSphere x ∈ d.physicalDomain
    rwa [heq]
  change openZeroExtension Ω w x = quotientPlaneRepresentative d w (π z)
  rw [openZeroExtension_eq hx, ← heq]
  exact (quotientPlaneRepresentative_plane d w π he hx).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneRepresentativeBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and unit bounds for the descended physical representative. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem sphereFromPlaneFunction_mem_Icc {G : Set Sphere} {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ physicalPlaneDomain G, w x ∈ Icc 0 1) :
    ∀p ∈ G, sphereFromPlaneFunction w p ∈ Icc 0 1 := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => simp [sphereFromPlaneFunction]
  | coe z =>
    rw [sphereFromPlaneFunction_coe]
    apply hw
    change (complexPlaneCoordinates (complexPlaneCoordinates.symm z) : Sphere) ∈ G
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

theorem quotientPlaneRepresentative_mem_Icc (d : PathCodeData X Sphere) {w : EuclideanPlane → ℝ}
    (hw : ∀x ∈ physicalPlaneDomain d.physicalDomain, w x ∈ Icc 0 1) :
    ∀x, quotientPlaneRepresentative d w x ∈ Icc 0 1 := by
  classical
  intro x
  by_cases hx : x ∈ d.quotientDomain
  · rw [quotientPlaneRepresentative, dite_eq_left hx]
    exact sphereFromPlaneFunction_mem_Icc hw _ (d.domainEquiv.symm ⟨x, hx⟩).property
  · simp only [quotientPlaneRepresentative, dite_eq_right hx, mem_Icc, le_refl, zero_le_one, and_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SpherePlaneContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported planar smoothing descends continuously across infinity. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem quotientPlaneRepresentative_continuousOn
    (d : PathCodeData X Sphere) (w : EuclideanPlane → ℝ)
    (hw : ContinuousOn (sphereFromPlaneFunction w) d.physicalDomain) :
    ContinuousOn (quotientPlaneRepresentative d w) d.quotientDomain := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hh : Continuous (fun x : d.quotientDomain =>
      sphereFromPlaneFunction w (d.domainEquiv.symm x).val) :=
    hw.domRestrict.comp d.domainEquiv.symm.continuous
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change quotientPlaneRepresentative d w x.val = _
  exact dite_eq_left x.property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalRealCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine continuous quotient coordinate with its smooth finite-energy
physical representative, ready for finite transfer. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem physicalRealCoordinate_of_plane_smoothing
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (hunit : ∀x ∈ physicalPlaneDomain d.physicalDomain, w x ∈ Icc 0 1)
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain)))
    {K : Set EuclideanPlane} (hK : IsCompact K) (hzero : ∀x ∉ K, w x = 0) :
    ∃Q : PhysicalRealCoordinate d π, Q.quotient = quotientPlaneRepresentative d w ∧
      ∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) := by
  obtain ⟨v, hm, hs, hew, hnorm, hp⟩ := exists_real_physical_representative d hG π he w hw henergy
  refine ⟨{
    quotient := quotientPlaneRepresentative d w
    quotient_continuous := quotientPlaneRepresentative_continuousOn d w
      (sphereFromPlaneFunction_continuousOn hG hw.continuousOn hK hzero)
    quotient_unit := quotientPlaneRepresentative_mem_Icc d hunit
    physical := v
    physical_measurable := hm
    physical_smooth := hs
    physical_energy := hew
    pullback := hp }, rfl, hnorm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoordinateGradientSize
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spherical Dirichlet norm is bounded by the two physical partial
norms used by the barrier construction, on the same measurable region. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem spherical_gradient_norm_le_partial_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → ℝ}
    (hf : MemLp (FiniteTransfer.planarGradient f) 2 μ) :
    Real.sqrt (∫x, FiniteTransfer.gradientEnergy f
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x ∂μ) ≤
      (eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ).toReal +
      (eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ).toReal := by
  rw [spherical_gradient_energy_eq_norms hf, Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => (fderiv ℝ f x) (1, 0)) 2 μ)
    have hy := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => (fderiv ℝ f x) (0, 1)) 2 μ)
    nlinarith [mul_nonneg hx hy]

theorem physical_coordinate_gradient_size_le
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (π : Sphere → X) (Q : PhysicalRealCoordinate d π)
    {S : Set (ℝ × ℝ)} (hS : S ⊆ FiniteTransfer.realChartDomain d.physicalDomain)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀i : Fin 2, eLpNorm (fun x => (fderiv ℝ Q.physical x)
      (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) ≤ A) :
    Real.sqrt (∫x in S, FiniteTransfer.gradientEnergy Q.physical
      (fun z => FiniteTransfer.sphericalMetricFactor z • 1) x) ≤ 2 * A.toReal := by
  have henergy := Q.physical_energy.mono_measure (Measure.restrict_mono_set volume hS)
  have hzero := ENNReal.toReal_mono hA (hbound 0)
  have hone := ENNReal.toReal_mono hA (hbound 1)
  have hroot := spherical_gradient_norm_le_partial_norms henergy
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero] at hzero hone
  linarith


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
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleArcToll
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An injective arc pays each boundary weight at most once. The payment
is bounded by the actual atomic measure on any set containing the arc. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem atomicBoundaryMeasure_apply {X : Type*} [MeasurableSpace X]
    (m : X → ℝ≥0∞) {S : Set X} (hS : MeasurableSet S) :
    atomicBoundaryMeasure m S = ∑'x, S.indicator m x := by
  classical
  rw [atomicBoundaryMeasure, Measure.sum_apply _ hS]
  apply tsum_congr
  intro x
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS]
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

theorem atomicBoundaryMeasure_null {X : Type*} [MeasurableSpace X]
    (m : X → ℝ≥0∞) {S : Set X} (hS : MeasurableSet S)
    (hm : ∀x ∈ S, m x = 0) : atomicBoundaryMeasure m S = 0 := by
  rw [atomicBoundaryMeasure_apply m hS]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx, hm x hx]
  · exact indicator_of_notMem hx m

theorem simple_arc_boundary_toll_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (γ : C(PathTime, X)) (hinj : Injective γ) (m : X → ℝ≥0∞)
    {S : Set X} (hS : MeasurableSet S) (hγ : range γ ⊆ S) :
    boundaryToll γ m ≤ atomicBoundaryMeasure m S := by
  rw [boundaryToll, atomicBoundaryMeasure_apply m hS]
  calc
    (∑'t, m (γ t)) = ∑'t, S.indicator m (γ t) := by
      apply tsum_congr
      intro t
      rw [indicator_of_mem (hγ (mem_range_self t))]
    _ ≤ ∑'x, S.indicator m x := ENNReal.tsum_comp_le_tsum_of_injective hinj _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AtomicLevelFiniteness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-summable point weights and level-incidence bounds give finite
atomic payment on almost every prior level. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem ae_finite_atomic_level_payment
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure T) (H : T → Set X)
    (hH : ∀t, MeasurableSet (H t))
    (hsection : ∀x, MeasurableSet {t | x ∈ H t})
    (m a : X → ℝ≥0∞)
    (hm : (∑'x, m x ^ 2) ≠ ∞) (ha : (∑'x, a x ^ 2) ≠ ∞)
    (hincidence : ∀x, ν {t | x ∈ H t} ≤ a x) :
    ∀ᵐt ∂ν, atomicBoundaryMeasure m (H t) < ∞ := by
  have hcount : (support m).Countable := by
    simpa only [support, ne_eq, sq_eq_zero_iff] using
      (Summable.countable_support_ennreal hm)
  let : Countable (support m) := hcount.to_subtype
  let L : T → ℝ≥0∞ := fun t => ∑'x : support m,
    ({t | x.val ∈ H t}).indicator (fun _ => m x.val) t
  have hL : Measurable L := Measurable.tsum fun x =>
    measurable_const.indicator (hsection x.val)
  have hmass (t : T) : atomicBoundaryMeasure m (H t) = L t := by
    rw [atomicBoundaryMeasure_apply m (hH t)]
    have he : (∑'x : support m, (H t).indicator m x.val) = ∑'x, (H t).indicator m x := by
      apply tsum_subtype_eq_of_support_subset
      intro x hx
      by_contra hmzero
      have hz : m x = 0 := not_not.mp hmzero
      simp only [mem_support] at hx
      exact hx (by simp [hz])
    rw [← he]
    apply tsum_congr
    intro x
    by_cases hx : x.val ∈ H t <;> simp [hx]
  have hfinite : (∫⁻t, L t ∂ν) < ∞ := by
    calc
      _ = ∑'x : support m, m x.val * ν {t | x.val ∈ H t} := by
        rw [show (∫⁻t, L t ∂ν) =
          ∫⁻t, ∑'x : support m, ({t | x.val ∈ H t}).indicator (fun _ => m x.val) t ∂ν from rfl,
          lintegral_tsum]
        · exact tsum_congr fun x => lintegral_indicator_const (hsection x.val) _
        · intro x
          exact (measurable_const.indicator (hsection x.val)).aemeasurable
      _ ≤ ∑'x : support m, (m x.val ^ 2 + a x.val ^ 2) := by
        apply ENNReal.tsum_le_tsum
        intro x
        exact (mul_le_mul_right (hincidence x.val) (m x.val)).trans
          (ennreal_mul_le_sq_add_sq (m x.val) (a x.val))
      _ = (∑'x : support m, m x.val ^ 2) + ∑'x : support m, a x.val ^ 2 :=
        ENNReal.tsum_add
      _ ≤ (∑'x, m x ^ 2) + ∑'x, a x ^ 2 := add_le_add
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun x : support m => (x.val : X)) Subtype.val_injective (fun x => m x ^ 2))
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun x : support m => (x.val : X)) Subtype.val_injective (fun x => a x ^ 2))
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hm.lt_top, ha.lt_top⟩
  filter_upwards [ae_lt_top hL hfinite.ne] with t ht
  rwa [hmass]

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Probability_LevelPaymentMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure used for the free-trace argument is constructed from
physical weighted length and actual boundary atoms on the prior level set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem levelPaymentMeasure_finite {X Y : Type*}
    [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (hπ : Measurable π) (G : Set Y) (H : Set X)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hg : (∫⁻y in G ∩ π ⁻¹' H, g y ∂(μH[1] : Measure Y)) < ∞)
    (hm : atomicBoundaryMeasure m H < ∞) :
    IsFiniteMeasure (levelPaymentMeasure π G H g m) := by
  constructor
  rw [levelPaymentMeasure, Measure.add_apply, Measure.map_apply hπ MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_apply_univ, setLIntegral_univ]
  exact ENNReal.add_lt_top.mpr ⟨hg, hm⟩

theorem levelPaymentMeasure_free_null {X Y : Type*}
    [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Y → X) (hπ : Measurable π) {G : Set Y} {U B H F : Set X}
    (hF : MeasurableSet F)
    (hπG : MapsTo π G U) (hUB : Disjoint U B) (hFB : F ⊆ B)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (hm : ∀x ∈ F, m x = 0) :
    levelPaymentMeasure π G H g m F = 0 := by
  have he : π ⁻¹' F ∩ (G ∩ π ⁻¹' H) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyF, hyG, _⟩
    exact Set.disjoint_left.mp hUB (hπG hyG) (hFB hyF)
  have hphysical : (((μH[1] : Measure Y).restrict (G ∩ π ⁻¹' H)).withDensity g).map π F = 0 := by
    rw [Measure.map_apply hπ hF, withDensity_apply _ (hF.preimage hπ),
      Measure.restrict_restrict (hF.preimage hπ), he, Measure.restrict_empty, lintegral_zero_measure]
  have hatomic : (atomicBoundaryMeasure m).restrict H F = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      _ ≤ atomicBoundaryMeasure m F := Measure.restrict_apply_le _ _
      _ = 0 := atomicBoundaryMeasure_null m hF hm
  rw [levelPaymentMeasure, Measure.add_apply, hphysical, hatomic, zero_add]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SimpleArcLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of an injective arc is paid by the Hausdorff length of
its image. Disjoint parameter intervals have disjoint half-open images. -/

open Set Function MeasureTheory Metric
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_edist_le_length_Ioc
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) {a b : PathTime} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≤ b) : edist (f b) (f a) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hsub : Icc a b ⊆ s := hs.out ha hb
  have hc : IsPreconnected (f '' Icc a b) :=
    isPreconnected_Icc.image f (hf.mono hsub)
  have hd := dist_le_hausdorffMeasure_one_of_preconnected hc
    (mem_image_of_mem f (left_mem_Icc.mpr hab))
    (mem_image_of_mem f (right_mem_Icc.mpr hab))
  rw [edist_dist]
  apply hd.trans
  have hi : f '' Icc a b ⊆ insert (f a) (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (insert (f a) (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) :=
      measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem simple_arc_variation_le_length
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : PathTime → X) {s : Set PathTime} (hs : OrdConnected s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    eVariationOn f s ≤ (μH[1] : Measure X) (f '' s) := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  let A : ℕ → Set X := fun i => f '' Ioc (u i) (u (i + 1))
  have hA (i : ℕ) : MeasurableSet (A i) := by
    have hsub : Icc (u i) (u (i + 1)) ⊆ s := hs.out (hus i) (hus (i + 1))
    have hcompact : IsCompact (f '' Icc (u i) (u (i + 1))) :=
      isCompact_Icc.image_of_continuousOn (hf.mono hsub)
    have he : A i = f '' Icc (u i) (u (i + 1)) \ {f (u i)} := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
        intro heq
        exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht)) (hus i) heq)
      · rintro ⟨⟨t, ht, rfl⟩, hne⟩
        refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
        intro heq
        exact hne (congrArg f heq.symm)
    rw [he]
    exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)
  have hdis : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨v, hv, heq⟩
    have hts : t ∈ s := hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht)
    have hvs : v ∈ s := hs.out (hus j) (hus (j + 1)) (Ioc_subset_Icc_self hv)
    have htv : t = v := hinj hts hvs heq.symm
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt_of_ge (ht.2.trans (hu (Nat.succ_le_of_lt hij)))) (htv ▸ hv.1)
    · exact (not_lt_of_ge (hv.2.trans (hu (Nat.succ_le_of_lt hji)))) (htv.symm ▸ ht.1)
  calc
    _ ≤ ∑ i ∈ Finset.range n, (μH[1] : Measure X) (A i) := by
      apply Finset.sum_le_sum
      intro i _
      exact simple_arc_edist_le_length_Ioc f hs hf (hus i) (hus (i + 1))
        (hu (Nat.le_succ i))
    _ = (μH[1] : Measure X) (⋃ i ∈ Finset.range n, A i) := by
      rw [measure_biUnion_finset (fun i _ j _ hij => hdis hij) (fun i _ => hA i)]
    _ ≤ (μH[1] : Measure X) (f '' s) := by
      apply measure_mono
      intro x hx
      obtain ⟨i, _, t, ht, rfl⟩ := mem_iUnion₂.mp hx
      exact ⟨t, hs.out (hus i) (hus (i + 1)) (Ioc_subset_Icc_self ht), rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathHausdorffLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every continuous path has image Hausdorff length at most its metric
variation. Small dyadic images supply the covers in the definition. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_small_dyadic_images {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hp)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hz).2 δ hδ).exists
  refine ⟨n, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

theorem path_hausdorff_length_le_variation {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (γ : C(PathTime, X)) :
    (μH[1] : Measure X) (range γ) ≤ eVariationOn γ univ := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  choose k hk using fun n => exists_small_dyadic_images γ (hr n)
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ '' Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)
  have hcover (n : ℕ) : range γ ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, hi, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (range γ)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall hk) (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [] with n
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤
        ∑ i : Fin (2 ^ k n), eVariationOn γ (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) := by
      apply Finset.sum_le_sum
      intro i _
      apply ediam_le
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      exact eVariationOn.edist_le γ hs ht
    _ = _ := sum_dyadic_variations γ (k n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SimpleArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arclength occupation of an injective continuous path. This
identifies weighted path cost with the Hausdorff integral on its image. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_variation_eq_hausdorff_interval
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : C(PathTime, X)) {a b : PathTime} (hab : a ≤ b)
    (hinj : InjOn γ (Icc a b)) :
    eVariationOn γ (Icc a b) = (μH[1] : Measure X) (γ '' Icc a b) := by
  apply le_antisymm
  · exact simple_arc_variation_le_length γ ordConnected_Icc γ.continuous.continuousOn hinj
  · have h := path_hausdorff_length_le_variation (γ.comp (timeClip a b))
    rw [variation_timeClip γ hab] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    rw [ContinuousMap.coe_comp, range_comp, range_timeClip hab]

theorem simple_arc_length_measure
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathLengthMeasure γ = (μH[1] : Measure X).comap γ.val := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  apply Measure.ext_of_Icc
  intro a b hab
  rw [pathLengthMeasure_Icc γ hab, he.comap_apply]
  exact arc_variation_eq_hausdorff_interval γ.val hab hinj.injOn

theorem simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) (hinj : Injective γ.val) :
    pathOccupation γ = (μH[1] : Measure X).restrict (range γ.val) := by
  have he : MeasurableEmbedding γ.val := γ.val.continuous.isClosedEmbedding hinj |>.measurableEmbedding
  rw [pathOccupation, simple_arc_length_measure γ hinj]
  exact he.map_comap _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_DisjointArcLengths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint compact portions of a simple arc have a total length bounded
by the Hausdorff length of the whole arc, even when the map is only
continuous on an open part of its parameter domain. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_Ioc_image_measurable
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    MeasurableSet (f '' Ioc a b) := by
  have hcompact : IsCompact (f '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn (hf.mono hsub)
  have he : f '' Ioc a b = f '' Icc a b \ {f a} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, ?_⟩
      intro heq
      exact ht.1.ne' (hinj (hsub (Ioc_subset_Icc_self ht))
        (hsub (left_mem_Icc.mpr hab)) heq)
    · rintro ⟨⟨t, ht, rfl⟩, hne⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
      intro heq
      exact hne (congrArg f heq.symm)
  rw [he]
  exact hcompact.isClosed.measurableSet.diff (measurableSet_singleton _)

theorem simple_arc_variation_le_Ioc_image
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    {a b : PathTime} (_hab : a ≤ b) (hsub : Icc a b ⊆ V) :
    eVariationOn f (Icc a b) ≤ (μH[1] : Measure X) (f '' Ioc a b) := by
  let : NullSingletonClass (μH[1] : Measure X) :=
    Measure.nullSingletonClass_hausdorff X (by norm_num)
  have hi : f '' Icc a b ⊆ {f a} ∪ (f '' Ioc a b) := by
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.1.eq_or_lt with h | h
    · exact Or.inl (congrArg f h.symm)
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  calc
    _ ≤ (μH[1] : Measure X) (f '' Icc a b) :=
      simple_arc_variation_le_length f ordConnected_Icc (hf.mono hsub) (hinj.mono hsub)
    _ ≤ (μH[1] : Measure X) ({f a} ∪ (f '' Ioc a b)) := measure_mono hi
    _ ≤ (μH[1] : Measure X) {f a} + (μH[1] : Measure X) (f '' Ioc a b) := measure_union_le _ _
    _ = _ := by rw [measure_singleton, zero_add]

theorem sum_disjoint_arc_variations_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, eVariationOn f (Icc (a i) (b i))) ≤ (μH[1] : Measure X) (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ ≤ ∑ i, (μH[1] : Measure X) (f '' Ioc (a i) (b i)) :=
      Finset.sum_le_sum (fun i _ => simple_arc_variation_le_Ioc_image f hf hinj (hab i) (hsub i))
    _ = (μH[1] : Measure X) (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [measure_iUnion himdis (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        tsum_fintype]
    _ ≤ _ := measure_mono (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ArcImageMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint portions of a simple arc have disjoint image measures after
their shared endpoints, which have zero Hausdorff length, are removed. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem arc_image_Icc_ae_eq_Ioc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NullSingletonClass μ] (f : PathTime → X) (a b : PathTime) :
    f '' Icc a b =ᵐ[μ] f '' Ioc a b := by
  filter_upwards [μ.ae_ne (f a)] with x hx
  apply propext
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, ht.2⟩, rfl⟩
    intro heq
    exact hx (congrArg f heq.symm)
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Ioc_subset_Icc_self ht, rfl⟩

theorem sum_disjoint_arc_image_measures_le {ι X : Type*} [Fintype ι]
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [NullSingletonClass μ]
    {V : Set PathTime} (f : PathTime → X) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (a b : ι → PathTime) (hab : ∀ i, a i ≤ b i)
    (hsub : ∀ i, Icc (a i) (b i) ⊆ V)
    (hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    (∑ i, μ.restrict (f '' Icc (a i) (b i))) ≤ μ.restrict (f '' V) := by
  have himdis : Pairwise (fun i j => Disjoint
      (f '' Ioc (a i) (b i)) (f '' Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, heq⟩
    have hts := hinj (hsub i (Ioc_subset_Icc_self ht)) (hsub j (Ioc_subset_Icc_self hs)) heq.symm
    exact Set.disjoint_left.mp (hdis hij) ht (hts.symm ▸ hs)
  calc
    _ = ∑ i, μ.restrict (f '' Ioc (a i) (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Measure.restrict_congr_set (arc_image_Icc_ae_eq_Ioc μ f (a i) (b i))
    _ = μ.restrict (⋃ i, f '' Ioc (a i) (b i)) := by
      rw [Measure.restrict_iUnion himdis
        (fun i => simple_arc_Ioc_image_measurable f hf hinj (hab i) (hsub i)),
        Measure.sum_fintype]
    _ ≤ _ := Measure.restrict_mono
      (iUnion_subset fun i => image_mono (Ioc_subset_Icc_self.trans (hsub i))) le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PartialSimpleArcLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite physical length of a simple quotient arc follows from the
Hausdorff length of its physical part. No boundary extension of its
physical lift is required. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem partial_simple_arc_dyadic_sum_le
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {V : Set PathTime} (f : PathTime → Y) (hf : ContinuousOn f V) (hinj : InjOn f V)
    (n : ℕ) :
    (∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
      eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0) ≤
      (μH[1] : Measure Y) (f '' V) := by
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V}
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have h := sum_disjoint_arc_variations_le f hf hinj
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis
  have he : (∑ i : J, eVariationOn f (Icc (dyadicLeft n i.val) (dyadicRight n i.val))) =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V then
        eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    simpa only [tsum_fintype, J, Set.indicator_apply, Set.mem_ofPred_eq] using
      tsum_subtype J (fun i => eVariationOn f (Icc (dyadicLeft n i) (dyadicRight n i)))
  rwa [he] at h

theorem physicalValue_path_continuousOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    ContinuousOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h : Continuous (fun t : γ ⁻¹' U => (e.symm ⟨γ t.val, t.property⟩).val) :=
    continuous_subtype_val.comp (e.symm.continuous.comp
      ((γ.continuous.comp continuous_subtype_val).subtype_mk _))
  apply h.congr
  intro t
  change (e.symm ⟨γ t.val, t.property⟩).val = physicalValue e y₀ (γ t.val)
  rw [physicalValue, dite_eq_left (show γ t.val ∈ U from t.property)]

theorem physicalValue_path_injOn
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    InjOn (physicalValue e y₀ ∘ γ) (γ ⁻¹' U) := by
  intro s hs t ht heq
  change γ s ∈ U at hs
  change γ t ∈ U at ht
  apply hγ
  simp only [Function.comp_apply, physicalValue, dite_eq_left hs, dite_eq_left ht] at heq
  have hsub : e.symm ⟨γ s, hs⟩ = e.symm ⟨γ t, ht⟩ := Subtype.ext heq
  exact congrArg Subtype.val (e.symm.injective hsub)

theorem physicalSubpath_variation_eq_value
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) {a b : PathTime}
    (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    eVariationOn (physicalSubpath e hab ⟨γ, hγ⟩) univ =
      eVariationOn (physicalValue e y₀ ∘ γ) (Icc a b) := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    simp only [Function.comp_apply, physicalSubpath, ContinuousMap.coe_mk,
      physicalValue, dite_eq_left (hγ ht)]
  rw [he, eVariationOn.comp_eq_of_monotoneOn _ _
    ((monotone_timeClip a b).monotoneOn univ), image_univ, range_timeClip hab]

theorem simple_quotient_arc_physical_length_le
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (hγ : Injective γ) :
    physicalDomainLength e y₀ γ ≤
      (μH[1] : Measure Y) ((physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U)) := by
  apply iSup_le
  intro n
  have he : physicalStageLength e y₀ n γ =
      ∑ i : Fin (2 ^ n), if Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U then
        eVariationOn (physicalValue e y₀ ∘ γ) (Icc (dyadicLeft n i) (dyadicRight n i)) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    · have hi' : Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i γ hi,
        physicalSubpath_variation_eq_value e y₀ γ _ hi, ite_eq_left hi']
    · have hi' : ¬ Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ ⁻¹' U := hi
      simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath,
        dite_eq_right hi, ite_eq_right hi']
      exact (eVariationOn.eq_zero_iff _).mpr (fun _ _ _ _ => edist_self _)
  rw [he]
  exact partial_simple_arc_dyadic_sum_le _ (physicalValue_path_continuousOn e y₀ γ)
    (physicalValue_path_injOn e y₀ γ hγ) n

theorem simple_quotient_arc_physical_length_le_preimage
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (y₀ : Y) (π : Y → X)
    (hπ : ∀y : G, π y.val = (e y).val)
    (γ : C(PathTime, X)) (hγ : Injective γ) {H : Set X} (hγH : range γ ⊆ H) :
    physicalDomainLength e y₀ γ ≤ (μH[1] : Measure Y) (π ⁻¹' H ∩ G) := by
  apply (simple_quotient_arc_physical_length_le e y₀ γ hγ).trans
  apply measure_mono
  rintro y ⟨t, ht, rfl⟩
  change γ t ∈ U at ht
  change π (physicalValue e y₀ (γ t)) ∈ H ∧ physicalValue e y₀ (γ t) ∈ G
  simp only [physicalValue, dite_eq_left ht]
  refine ⟨?_, (e.symm ⟨γ t, ht⟩).property⟩
  rw [hπ]
  simpa only [Homeomorph.apply_symm_apply] using hγH (mem_range_self t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectifiableSubarcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual short rectifiable arcs between nearby parameters of a
finite-cost curve, with either orientation. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathOccupation (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val := by
  rw [pathOccupation, pathLengthMeasure_affine]
  change (((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map (affineRestrictedPath a b γ.val).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (affinePathTime a b (rescalePathTime a b t)) = γ.val t
  rw [affine_rescalePathTime hab ht]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClippedArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A path that is injective only on a retained parameter interval has
exact Hausdorff occupation on that portion. Constant tails add no mass. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_portion_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathPortionOccupation γ a b = (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  let β := affineRectifiablePath γ hab
  have hβ : Injective β.val := by
    intro s t h
    exact (affinePathTime_strictMono hab).injective
      (hinj (affinePathTime_mem_Icc hab.le s) (affinePathTime_mem_Icc hab.le t) h)
  have hrange : range β.val = γ.val '' Icc a b := by
    change range (γ.val ∘ affinePathTime a b) = _
    rw [range_comp, range_affinePathTime hab]
  change ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val = _
  rw [← pathOccupation_affine γ hab, simple_arc_occupation β hβ, hrange]

theorem clipped_simple_arc_occupation
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (hinj : InjOn γ.val (Icc a b)) :
    pathOccupation (clippedPath γ hab.le) =
      (μH[1] : Measure X).restrict (γ.val '' Icc a b) := by
  rw [pathOccupation_clipped γ hab.le, simple_arc_portion_occupation γ hab hinj]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PhysicalSimpleArcPortion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact domain portion of an injective quotient path has exactly
the Hausdorff occupation of its physical lift. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem physical_simple_arc_portion_occupation
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) {a b : PathTime} (hab : a < b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    rectifiableOccupationCode (physicalSubpath e hab.le ⟨γ.val, hγ⟩) =
      (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' Icc a b) := by
  let β : RectifiablePath Y := ⟨physicalSubpath e hab.le ⟨γ.val, hγ⟩,
    physicalSubpath_rectifiable e hU hab.le γ.val hγ y₀ γ.property⟩
  have hβ : InjOn β.val (Icc a b) := by
    intro s hs t ht heq
    apply physicalValue_path_injOn e y₀ γ.val hinj (hγ hs) (hγ ht)
    exact (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ hs).trans
      (heq.trans (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm)
  have hclip : clippedPath β hab.le = β := by
    apply Subtype.ext
    exact physicalSubpath_comp_clip e hab.le ⟨γ.val, hγ⟩
  have himage : β.val '' Icc a b = (physicalValue e y₀ ∘ γ.val) '' Icc a b := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht⟩
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, ht, (physicalValue_subpath e y₀ hab.le ⟨γ.val, hγ⟩ ht).symm⟩
  rw [rectifiableOccupationCode_eq β.property]
  change pathOccupation β = _
  rw [← hclip, clipped_simple_arc_occupation β hab hβ, himage]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SimplePhysicalArcOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a simple quotient arc is bounded by Hausdorff
length on its physical image. This retains arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_physical_stage_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  let f := physicalValue e y₀ ∘ γ.val
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ.val ⁻¹' U}
  let : NullSingletonClass (μH[1] : Measure Y) :=
    Measure.nullSingletonClass_hausdorff Y (by norm_num)
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have he : physicalStageOccupation e y₀ n γ.val =
      ∑ i : J, (μH[1] : Measure Y).restrict
        (f '' Icc (dyadicLeft n i.val) (dyadicRight n i.val)) := by
    apply Finset.sum_congr_set J
    · intro i hi
      rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi]
      apply physical_simple_arc_portion_occupation e hU y₀ γ hinj _ hi
      change (i.val : ℝ) / (2 : ℝ) ^ n < ((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
      exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val) (by positivity)
    · intro i hi
      have hi' : γ.val ∉ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i) := hi
      simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hi',
        rectifiableOccupationCode_const]
  rw [he]
  exact sum_disjoint_arc_image_measures_le (μH[1] : Measure Y) f
    (physicalValue_path_continuousOn e y₀ γ.val) (physicalValue_path_injOn e y₀ γ.val hinj)
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis

theorem simple_arc_physical_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) :
    dyadicPhysicalOccupation e y₀ γ ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_le fun n => Measure.le_iff.mp
    (simple_arc_physical_stage_occupation_le e hU y₀ γ hinj n) S hS

theorem simple_arc_physical_integral_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) (g : Y → ℝ≥0∞) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ ≤
      ∫⁻ y in (physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U), g y ∂(μH[1] : Measure Y) :=
  lintegral_mono' (simple_arc_physical_occupation_le e hU y₀ γ hinj) le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SimpleArcPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical costs of a simple tagged arc are paid by the weighted
length and atomic boundary measure on the fixed prior level set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_cost_le_levelPaymentMeasure
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (hinj : Injective γ.val)
    {S : Set X} (hS : MeasurableSet S) (hγS : range γ.val ⊆ S)
    (hγH : range γ.val ⊆ H) :
    physicalTollCost d g m γ ≤ levelPaymentMeasure π d.physicalDomain H g m S := by
  have himage : (physicalValue d.domainEquiv d.basePoint ∘ γ.val) ''
      (γ.val ⁻¹' d.quotientDomain) ⊆ π ⁻¹' S ∩ (d.physicalDomain ∩ π ⁻¹' H) := by
    rintro y ⟨t, ht, rfl⟩
    change γ.val t ∈ d.quotientDomain at ht
    simp only [Function.comp_apply, physicalValue, dite_eq_left ht]
    have hproj : π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val = γ.val t := by
      rw [he]
      exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨γ.val t, ht⟩)
    refine ⟨?_, (d.domainEquiv.symm ⟨γ.val t, ht⟩).property, ?_⟩
    · change π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val ∈ S
      rw [hproj]
      exact hγS (mem_range_self t)
    · change π (d.domainEquiv.symm ⟨γ.val t, ht⟩).val ∈ H
      rw [hproj]
      exact hγH (mem_range_self t)
  have hphysical : (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) ≤
      (((μH[1] : Measure Y).restrict (d.physicalDomain ∩ π ⁻¹' H)).withDensity g).map π S := by
    rw [Measure.map_apply hπ hS, withDensity_apply _ (hS.preimage hπ),
      Measure.restrict_restrict (hS.preimage hπ)]
    exact (simple_arc_physical_integral_le d.domainEquiv hU d.basePoint γ hinj g).trans
      (lintegral_mono' (Measure.restrict_mono himage le_rfl) le_rfl)
  have hatomic : boundaryToll γ.val m ≤ (atomicBoundaryMeasure m).restrict H S := by
    rw [Measure.restrict_apply hS]
    exact simple_arc_boundary_toll_le γ.val hinj m (hS.inter hH)
      (fun x hx => ⟨hγS hx, hγH hx⟩)
  rw [physicalTollCost, levelPaymentMeasure, Measure.add_apply]
  exact add_le_add hphysical hatomic

theorem simple_arc_cost_le_own_range
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (hinj : Injective γ.val)
    (hγH : range γ.val ⊆ H) :
    physicalTollCost d g m γ ≤ levelPaymentMeasure π d.physicalDomain H g m (range γ.val) := by
  have hmeas : MeasurableSet (range γ.val) :=
    (isCompact_range γ.val.continuous).isClosed.measurableSet
  exact simple_arc_cost_le_levelPaymentMeasure d hU π hπ he (H := H) hH g m γ hinj
    (S := range γ.val) hmeas (fun _ hx => hx) hγH

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FullIntervalTag
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple arc in a permitted finite level union can use one tag on its
whole open parameter interval. If its endpoints are in the domain, no dust
time remains and every residual constraint is vacuous. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem fullIntervalTag_rules {X : Type*} [MetricSpace X]
    (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hinj : Injective γ)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀ t, ∃ i, (levels i, γ t) ∈ H (labels i)) :
    TagRules H N (fullIntervalTaggedPath γ n labels levels) := by
  intro k
  by_cases hk : k = 0
  · subst k
    change (γ, fullIntervalTag n labels levels) ∈ validTagShape ∧
      (γ, fullIntervalTag n labels levels) ∈ tagContainment H ∧
      fullIntervalTag n labels levels ∉ tagTupleExcluded N
    refine ⟨Or.inr ?_, ?_, ?_⟩
    · let s : PathTime := ⟨1 / 3, by constructor <;> norm_num⟩
      let t : PathTime := ⟨2 / 3, by constructor <;> norm_num⟩
      refine ⟨s, t, ?_, ?_, ?_, ?_, ?_⟩
      · change (0 : ℝ) < 1 / 3; norm_num
      · change (1 / 3 : ℝ) < 1; norm_num
      · change (0 : ℝ) < 2 / 3; norm_num
      · change (2 / 3 : ℝ) < 1; norm_num
      · intro heq
        have := congrArg Subtype.val (hinj heq)
        norm_num [s, t] at this
    · intro t _ _
      exact hlevel t
    · exact fun h => hN ((active_mem_tagTupleExcluded_iff N _).mp h)
  · simpa only [fullIntervalTaggedPath, hk, ite_false, if_false] using inactiveTag_rules H N γ

theorem residualTimes_fullIntervalTaggedPath {X : Type*} [TopologicalSpace X]
    {B : Set X} (γ : C(PathTime, X))
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (h0 : γ ⊥ ∉ B) (h1 : γ ⊤ ∉ B) :
    residualTimes B (fullIntervalTaggedPath γ n labels levels) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨htB, ht⟩
  change γ t ∈ B at htB
  have ht0 := ht 0
  change t ≤ (⊥ : PathTime) ∨ (⊤ : PathTime) ≤ t at ht0
  rcases ht0 with ht0 | ht1
  · exact h0 (by simpa only [le_bot_iff.mp ht0] using htB)
  · exact h1 (by simpa only [top_le_iff.mp ht1] using htB)

theorem residualConstraintFamily_of_empty {X Z : Type*} [MetricSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] {B : Set X} {Γ : TaggedPath X}
    (h : residualTimes B Γ = ∅) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞) :
    ResidualConstraintFamily B R P ν m Γ := by
  intro i n a b
  unfold ResidualIncidenceBound
  have he : {z | (Γ, z) ∈ residualIncidence B (Icc a.toTime b.toTime) (R i) (P i n)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨t, ht, _⟩
    rw [h] at ht
    exact ht
  rw [he, measure_empty]
  exact bot_le

theorem fullIntervalTaggedPath_allowed {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hinj : Injective γ)
    (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀ t, ∃ i, (levels i, γ t) ∈ d.levels (labels i))
    (h0 : γ ⊥ ∉ d.dust) (h1 : γ ⊤ ∉ d.dust) :
    AllowedTaggedPath d ν N (fullIntervalTaggedPath γ n labels levels) := by
  have he := residualTimes_fullIntervalTaggedPath γ n labels levels h0 h1
  refine ⟨hfin, fullIntervalTag_rules d.levels N γ hinj n labels levels hN hlevel,
    residualConstraintFamily_of_empty he _ _ _ _,
    residualConstraintFamily_of_empty he _ _ _ _, ?_⟩
  rw [residualImage, he, image_empty, measure_empty]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RawArcPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a simple arc to domain endpoints makes its full-interval
tag admissible. The actual barrier inequality then extends to free traces. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

section
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem raw_simple_physical_arc_domain_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hinj : Injective γ.val) (hγH : range γ.val ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ.val t) ∈ d.levels (labels i))
    (h0 : γ.val ⊥ ∈ d.quotientDomain) (h1 : γ.val ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |u (γ.val ⊤) - u (γ.val ⊥)| ≤
      4 * levelPaymentMeasure π d.physicalDomain H g m (range γ.val) := by
  let Γ : TaggedPhysicalPath d := (γ, (fullIntervalTaggedPath γ.val n labels levels).2)
  have hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2) :=
    fullIntervalTaggedPath_allowed d ν N γ.val hinj γ.property n labels levels hN hlevel
      (fun h => Set.disjoint_left.mp hdisj h0 h)
      (fun h => Set.disjoint_left.mp hdisj h1 h)
  have hcost : physicalTollCost d g m γ ≤
      levelPaymentMeasure π d.physicalDomain H g m (range γ.val) :=
    simple_arc_cost_le_own_range d hU π hπ he hH g m γ hinj hγH
  have hp : ENNReal.ofReal |u (γ.val ⊤) - u (γ.val ⊥)| ≤ 4 * physicalTollCost d g m γ :=
    hpay Γ hΓ h0 h1
  exact hp.trans (mul_le_mul_right hcost 4)

theorem raw_simple_arc_domain_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : C(PathTime, X)) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i))
    (h0 : γ ⊥ ∈ d.quotientDomain) (h1 : γ ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |u (γ ⊤) - u (γ ⊥)| ≤
      4 * levelPaymentMeasure π d.physicalDomain H g m (range γ) := by
  have hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞ :=
    (simple_quotient_arc_physical_length_le_preimage d.domainEquiv d.basePoint π he
      γ hinj hγH).trans_lt hlength
  exact raw_simple_physical_arc_domain_payment d hU hdisj π hπ he hH g m ν N u hpay
    ⟨γ, hfin⟩ hinj hγH n labels levels hN hlevel h0 h1

theorem raw_simple_arc_domain_pair_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H : Set X} (hH : MeasurableSet H)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hfinite : IsFiniteMeasure (levelPaymentMeasure π d.physicalDomain H g m))
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (γ : C(PathTime, X)) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i)) :
    ∀p ∈ range γ ∩ d.quotientDomain, ∀q ∈ range γ ∩ d.quotientDomain,
      |u p - u q| ≤ 4 * (levelPaymentMeasure π d.physicalDomain H g m).real (range γ) := by
  let := hfinite
  let μ := levelPaymentMeasure π d.physicalDomain H g m
  have hforward : ∀a b : PathTime, a < b → γ a ∈ d.quotientDomain →
      γ b ∈ d.quotientDomain → |u (γ a) - u (γ b)| ≤ 4 * μ.real (range γ) := by
    intro a b hab ha hb
    let ρ := affineRestrictedPath a b γ
    have hρinj : Injective ρ := hinj.comp (affinePathTime_strictMono hab).injective
    have hρsub : range ρ ⊆ range γ := by
      rintro _ ⟨t, rfl⟩
      exact mem_range_self (affinePathTime a b t)
    have hρ0 : ρ ⊥ = γ a := congrArg γ (affinePathTime_zero a b)
    have hρ1 : ρ ⊤ = γ b := congrArg γ (affinePathTime_one a b)
    have hp := raw_simple_arc_domain_payment d hU hdisj π hπ he hH hlength g m ν N u
      hpay ρ hρinj (hρsub.trans hγH) n labels levels hN
      (fun t => hlevel (affinePathTime a b t)) (hρ0.symm ▸ ha) (hρ1.symm ▸ hb)
    rw [hρ0, hρ1, abs_sub_comm] at hp
    have hbound : ENNReal.ofReal |u (γ a) - u (γ b)| ≤ 4 * μ (range γ) :=
      hp.trans (mul_le_mul_right (measure_mono hρsub) 4)
    have hr := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _))).mp hbound
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, measureReal_def] using hr
  rintro p ⟨⟨a, rfl⟩, ha⟩ q ⟨⟨b, rfl⟩, hb⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact hforward a b hab ha hb
  · simpa only [sub_self, abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (measureReal_nonneg (μ := μ) (s := range γ))
  · simpa only [abs_sub_comm] using hforward b a hba hb ha

theorem raw_simple_arc_trace_payment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B : Set X} (hH : MeasurableSet H) (hB : IsTotallyDisconnected B)
    (hBU : Bᶜ ⊆ d.quotientDomain)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hfinite : IsFiniteMeasure (levelPaymentMeasure π d.physicalDomain H g m))
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    {x y : X} (γ : Path x y) (hinj : Injective γ) (hγH : range γ ⊆ H)
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels) (hlevel : ∀t, ∃i, (levels i, γ t) ∈ d.levels (labels i))
    {a b : ℝ} (ha : Tendsto u (𝓝[d.quotientDomain] x) (𝓝 a))
    (hb : Tendsto u (𝓝[d.quotientDomain] y) (𝓝 b)) :
    |a - b| ≤ 4 * (levelPaymentMeasure π d.physicalDomain H g m).real (range γ) := by
  apply simple_arc_boundary_payment hB hBU γ hinj u ha hb
  exact raw_simple_arc_domain_pair_payment d hU hdisj π hπ he hH hlength g m hfinite
    ν N u hpay γ.toContinuousMap hinj hγH n labels levels hN hlevel

end
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RawArcNullTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual raw barrier has a null free trace on every locally connected
compact subcontinuum of a good prior level union. The only arc-existence
input is the published connected-open specialization recorded in ArcNullImage. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem raw_barrier_null_trace_on_continuum
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Measurable π)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B F C : Set X} (hH : MeasurableSet H) (hB : IsTotallyDisconnected B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B) (hC : IsCompact C) (hCH : C ⊆ H)
    [LocallyConnectedSpace C] (harcs : HasSimpleArcsInConnectedOpens C)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hg : (∫⁻y in d.physicalDomain ∩ π ⁻¹' H, g y ∂(μH[1] : Measure Y)) < ∞)
    (hm : atomicBoundaryMeasure m H < ∞) (hmF : ∀x ∈ F, m x = 0)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u v : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (htrace : ∀x ∈ F, Tendsto u (𝓝[d.quotientDomain] x) (𝓝 (v x)))
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀x ∈ H, ∃i, (levels i, x) ∈ d.levels (labels i)) :
    volume (v '' (F ∩ C)) = 0 := by
  let μ := levelPaymentMeasure π d.physicalDomain H g m
  let : IsFiniteMeasure μ := levelPaymentMeasure_finite π hπ d.physicalDomain H g m hg hm
  have hπG : MapsTo π d.physicalDomain d.quotientDomain := by
    intro y hy
    rw [he ⟨y, hy⟩]
    exact (d.domainEquiv ⟨y, hy⟩).property
  have hμF : μ F = 0 := levelPaymentMeasure_free_null π hπ hF hπG hUB hFB g m hmF
  let μC : Measure C := μ.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : C → X) :=
    MeasurableEmbedding.subtype_coe hC.isClosed.measurableSet
  let : IsFiniteMeasure μC := ⟨by
    change μ.comap Subtype.val univ < ∞
    rw [hemb.comap_apply]
    exact measure_lt_top μ _⟩
  have hμCF : μC (Subtype.val ⁻¹' F) = 0 := by
    rw [show μC (Subtype.val ⁻¹' F) = μ (Subtype.val '' (Subtype.val ⁻¹' F)) from
      hemb.comap_apply μ _]
    exact measure_mono_null (image_preimage_subset _ _) hμF
  have hn : volume ((fun x : C => v x.val) '' (Subtype.val ⁻¹' F)) = 0 := by
    suffices h : volume ((fun x : C => v x.val) '' ((Subtype.val ⁻¹' F) ∩ univ)) = 0 by
      simpa only [inter_univ] using h
    apply null_image_of_simple_arc_payment (μ := μC) harcs isOpen_univ
      (by simpa only [inter_univ] using hμCF) (fun x : C => v x.val) (by norm_num : (0 : ℝ) ≤ 4)
    intro x hx y hy γ hγ _
    let δ : Path x.val y.val := γ.map continuous_subtype_val
    have hδ : Injective δ := Subtype.val_injective.comp hγ
    have hδH : range δ ⊆ H := by
      rintro z ⟨t, rfl⟩
      exact hCH (γ t).property
    have hp := raw_simple_arc_trace_payment d hU hdisj π hπ he hH hB hBU hlength
      g m inferInstance ν N u hpay δ hδ hδH n labels levels hN
      (fun t => hlevel _ (hCH (γ t).property)) (htrace x.val hx.1) (htrace y.val hy.1)
    have hmass : μC.real (range γ) = μ.real (range δ) := by
      rw [measureReal_def, measureReal_def, hemb.comap_apply]
      congr 1
      apply congrArg μ
      change Subtype.val '' range γ = range (Subtype.val ∘ γ)
      exact (range_comp _ _).symm
    rwa [hmass]
  have himage : (fun x : C => v x.val) '' (Subtype.val ⁻¹' F) = v '' (F ∩ C) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hxF, hxC⟩, rfl⟩
      exact ⟨⟨x, hxC⟩, hxF, rfl⟩
  rwa [himage] at hn

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RawLevelNullTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The raw barrier has Haar-null free trace on the nondegenerate components
of an actual compact quotient level union. The topology comes from finite
physical length. Arc existence uses only the connected-open specialization
of Lorimer (1981), recorded in `ArcNullImage`. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem raw_barrier_null_component_traces
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {H B F : Set X} (hH : IsCompact H) (hB : IsCompact B)
    (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hlength : (μH[1] : Measure Y) (π ⁻¹' H ∩ d.physicalDomain) < ∞)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hg : (∫⁻y in d.physicalDomain ∩ π ⁻¹' H, g y ∂(μH[1] : Measure Y)) < ∞)
    (hm : atomicBoundaryMeasure m H < ∞) (hmF : ∀x ∈ F, m x = 0)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u v : X → ℝ)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (htrace : ∀x ∈ F, Tendsto u (𝓝[d.quotientDomain] x) (𝓝 (v x)))
    (n : ℕ) (labels : Fin (n + 1) → ℕ) (levels : Fin (n + 1) → UnitAddCircle)
    (hN : levels ∉ N n labels)
    (hlevel : ∀x ∈ H, ∃i, (levels i, x) ∈ d.levels (labels i)) :
    HasFiniteLargeContinuumBound H ∧
      ∀ C : Set H, (∃x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : H => (v x.val : UnitAddCircle)) ''
          ((Subtype.val ⁻¹' F) ∩ C)) = 0 := by
  obtain ⟨hbound, _, hloc⟩ := level_topology_of_finite_physical_length
    π hπ hsurj hfiber hG hB hTD hbad hH hlength
  refine ⟨hbound, ?_⟩
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  rintro C ⟨x, rfl⟩ _
  let C := connectedComponent x
  have hC : IsCompact C := isClosed_connectedComponent.isCompact
  let : LocallyConnectedSpace C := hloc C hC isConnected_connectedComponent
  let A : Set X := Subtype.val '' C
  have hA : IsCompact A := hC.image continuous_subtype_val
  have hAH : A ⊆ H := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  let e : C ≃ₜ A := Topology.IsEmbedding.subtypeVal.homeomorphImage C
  let : LocallyConnectedSpace A := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hn := raw_barrier_null_trace_on_continuum d hU hdisj π hπ.measurable he
    hH.isClosed.measurableSet hTD hBU hUB hF hFB hA hAH (harcs A hA inferInstance)
    hlength g m hg hm hmF ν N u v hpay htrace n labels levels hN hlevel
  have himage : (fun z : H => (v z.val : UnitAddCircle)) ''
      ((Subtype.val ⁻¹' F) ∩ C) =
      ((↑) : ℝ → UnitAddCircle) '' (v '' (F ∩ A)) := by
    ext t
    constructor
    · rintro ⟨z, ⟨hzF, hzC⟩, rfl⟩
      exact ⟨v z.val, ⟨z.val, ⟨hzF, z, hzC, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨z, ⟨hzF, y, hyC, rfl⟩, rfl⟩, rfl⟩
      exact ⟨y, ⟨hzF, hyC⟩, rfl⟩
  rw [himage]
  exact volume_addCircle_image_eq_zero hn

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Modulus_RawBarrierCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility for the actual raw path-cost barrier. Finite level
payments and square-summable point incidences give the null component
traces; the only descriptive-set input is the cited finite-torus form of
Kechris's analytic-measurability theorem. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem raw_barrier_compatibility_of_finite_level_payments
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [MeasurableSpace C(PathTime, X)]
    (hLusin : FiniteTorusAnalyticMeasurability)
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Y → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {B F : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hF : MeasurableSet F) (hFB : F ⊆ B) (hFU : F ⊆ closure d.quotientDomain)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (R : ℕ → Set (X × UnitAddCircle)) (hR : ∀i, IsClosed (R i))
    (hRlevels : ∀i x t, (x, t) ∈ R i ↔ (t, x) ∈ d.levels i)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hlength : ∀i, ∀ᵐt ∂volume,
      (μH[1] : Measure Y) (d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ R i}) < ∞)
    (hg : ∀i, ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ R i}, g y
        ∂(μH[1] : Measure Y)) < ∞)
    (hm : (∑'x, m x ^ 2) ≠ ∞) (hmF : ∀x ∈ F, m x = 0)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hincidence : ∀i x, volume {t | (x, t) ∈ R i} ≤ d.levelWeights i x)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u v : X → ℝ) (hu : ∀x ∈ d.quotientDomain, |u x| ≤ 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (htrace : ∀x ∈ F, Tendsto u (𝓝[d.quotientDomain] x) (𝓝 (v x)))
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain u) R labels) = 0 := by
  let A : ℕ → UnitAddCircle → Set X := fun i t => {x | (x, t) ∈ R i}
  let H : (Fin (n + 1) → UnitAddCircle) → Set X :=
    fun θ => {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  have hHA (θ) : H θ = ⋃j, A (labels j) (θ j) := by
    ext x
    simp [H, A, finiteLevelUnionGraph]
  have hphysical (θ) : d.physicalDomain ∩ π ⁻¹' H θ =
      ⋃j, d.physicalDomain ∩ π ⁻¹' A (labels j) (θ j) := by
    rw [hHA, preimage_iUnion, inter_iUnion]
  have hlen := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => d.physicalDomain ∩ π ⁻¹' A i t) (fun _ => 1) labels
    (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hlength)
  have hweighted := ae_finite_lintegral_level_union (μH[1] : Measure Y) volume
    (fun i t => d.physicalDomain ∩ π ⁻¹' A i t) g labels hg
  have hatom (i : ℕ) : ∀ᵐt ∂volume, atomicBoundaryMeasure m (A i t) < ∞ := by
    apply ae_finite_atomic_level_payment volume (A i)
      (fun t => ((hR i).preimage (continuous_id.prodMk continuous_const)).measurableSet)
      (fun x => ((hR i).preimage (continuous_const.prodMk continuous_id)).measurableSet)
      m (d.levelWeights i) hm (hweights i) (hincidence i)
  have hatoms := ae_finite_lintegral_level_union (atomicBoundaryMeasure m) volume A
    (fun _ => 1) labels (by simpa only [lintegral_one, Measure.restrict_apply_univ] using hatom)
  have hgoodN : ∀ᵐθ ∂Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)),
      θ ∉ N n labels := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hN
  apply measure_freeComponentFailure_eq_zero hLusin (n + 1) hF
    (isCompact_circleBandGraph hu).isClosed hR labels (fun x => (v x : UnitAddCircle))
    (fun x hx _ => circleBandGraph_of_trace hu (hFU hx) (htrace x hx))
  filter_upwards [hlen, hweighted, hatoms, hgoodN] with θ hlenθ hgθ hmθ hNθ
  have hH : IsCompact (H θ) :=
    ((isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)).isCompact
  have hlenH : (μH[1] : Measure Y) (π ⁻¹' H θ ∩ d.physicalDomain) < ∞ := by
    simpa only [lintegral_one, Measure.restrict_apply_univ, ← hphysical, inter_comm] using hlenθ
  have hgH : (∫⁻y in d.physicalDomain ∩ π ⁻¹' H θ, g y ∂(μH[1] : Measure Y)) < ∞ := by
    rwa [← hphysical] at hgθ
  have hmH : atomicBoundaryMeasure m (H θ) < ∞ := by
    simpa only [lintegral_one, Measure.restrict_apply_univ, ← hHA] using hmθ
  exact raw_barrier_null_component_traces d hU hG hdisj π hπ hsurj hfiber he hH hB hTD
    hbad hBU hUB hF hFB harcs hlenH g m hgH hmH hmF ν N u v hpay htrace n labels θ hNθ
    (by intro x hx; obtain ⟨j, hj⟩ := mem_iUnion.mp (hHA θ ▸ hx)
        exact ⟨j, (hRlevels _ _ _).mp hj⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_BoundaryTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

theorem tendsto_boundaryTrace_of_zero_band
    {X : Type*} [TopologicalSpace X] {G : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ y ∈ G, |f y| ≤ M) {x : X} (hx : x ∈ closure G)
    (hband : limsup f (𝓝[G] x) - liminf f (𝓝[G] x) ≤ 0) :
    Tendsto f (𝓝[G] x) (𝓝 (realBoundaryTrace G f x)) := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hbounds : ∀ᶠ y in 𝓝[G] x, -M ≤ f y ∧ f y ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact abs_le.mp (hM y hy)
  have hlower : IsBoundedUnder (· ≥ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_ge (hbounds.mono (fun _ hy => hy.1))
  have hupper : IsBoundedUnder (· ≤ ·) (𝓝[G] x) f :=
    isBoundedUnder_of_eventually_le (hbounds.mono (fun _ hy => hy.2))
  have hle := liminf_le_limsup hupper hlower
  exact tendsto_of_liminf_eq_limsup rfl (by dsimp [realBoundaryTrace] <;> linarith)
    hupper hlower

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ENNRealBoundaryTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise trace convergence and the countable exceptional set for the
ENNReal dust budgets used by the constructed chain potential. -/

open Set Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity

theorem countable_square_toll_support {X : Type*} {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) : {x | m x ≠ 0}.Countable := by
  simpa only [Function.support, ne_eq, sq_eq_zero_iff] using
    (Summable.countable_support_ennreal hm)

theorem boundaryTrace_of_ennreal_budget
    {X : Type*} [TopologicalSpace X] {G B : Set X} {u : X → ℝ} {m : X → ℝ≥0∞}
    (hu : ∀x ∈ G, u x ∈ Icc 0 1) (hB : B ⊆ closure G)
    (hm : (∑' x, m x ^ 2) ≠ ∞)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[G] s) - liminf u (𝓝[G] s)) ≤ 4 * m s) :
    {x | m x ≠ 0}.Countable ∧ ∀s ∈ B, m s = 0 →
      Tendsto u (𝓝[G] s) (𝓝 (realBoundaryTrace G u s)) := by
  refine ⟨countable_square_toll_support hm, ?_⟩
  intro s hs hzero
  apply tendsto_boundaryTrace_of_zero_band (M := 1)
  · intro x hx
    rw [abs_of_nonneg (hu x hx).1]
    exact (hu x hx).2
  · exact hB hs
  · have h := hband s hs
    rw [hzero, mul_zero] at h
    exact ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BandContraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise contraction of boundary intervals preserves compatibility
of the new coordinate with the fixed earlier coordinates. -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem real_band_subset_of_liminf_limsup
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    (U : Set X) (u v : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (hv : ∀x, v x ∈ Icc 0 1)
    {x : X} (hx : x ∈ closure U)
    (hlo : liminf u (𝓝[U] x) ≤ liminf v (𝓝[U] x))
    (hhi : limsup v (𝓝[U] x) ≤ limsup u (𝓝[U] x)) :
    {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U v)} ⊆
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U u)} := by
  have hu' : ∀x ∈ U, |u x| ≤ 1 := fun x _ => abs_le.mpr ⟨by linarith [(hu x).1], (hu x).2⟩
  have hv' : ∀x ∈ U, |v x| ≤ 1 := fun x _ => abs_le.mpr ⟨by linarith [(hv x).1], (hv x).2⟩
  rw [intervalFiberHull_clusterGraph_eq_boundary_band hv' hx,
    intervalFiberHull_clusterGraph_eq_boundary_band hu' hx]
  exact Icc_subset_Icc hlo hhi

theorem circle_band_subset_of_real_band
    {X : Type*} [TopologicalSpace X] (U : Set X) (u v : X → ℝ) {x : X}
    (h : {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U v)} ⊆
      {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U u)}) :
    ∀t, (x, t) ∈ circleBandGraph U v → (x, t) ∈ circleBandGraph U u := by
  intro t ht
  obtain ⟨⟨y, r⟩, hr, heq⟩ := ht
  have hy : y = x := congrArg Prod.fst heq
  subst y
  exact ⟨(x, r), h hr, heq⟩

theorem freeComponentFailure_mono_new
    {X T J Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew Snew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hsub : ∀x ∈ F, ∀t, (x, t) ∈ Rnew → (x, t) ∈ Snew) :
    freeComponentFailure F Rnew R labels ⊆ freeComponentFailure F Snew R labels := by
  rintro t ⟨⟨x, s⟩, hx, heq⟩
  exact ⟨(x, s), ⟨hx.1, hsub x hx.1 s.1 hx.2.1, hx.2.2⟩, heq⟩

theorem band_contraction_preserves_compatibility
    {X T J Λ : Type*} [TopologicalSpace X]
    [TopologicalSpace T] [MeasurableSpace (T × (J → T))]
    (μ : Measure (T × (J → T))) (F : Set X)
    (Rnew Snew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ)
    (hsub : ∀x ∈ F, ∀t, (x, t) ∈ Rnew → (x, t) ∈ Snew)
    (hzero : μ (freeComponentFailure F Snew R labels) = 0) :
    μ (freeComponentFailure F Rnew R labels) = 0 :=
  measure_mono_null (freeComponentFailure_mono_new F Rnew Snew R labels hsub) hzero

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarDifferentialEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-transfer gradient energy controls the norm of the scalar
real differential in the complex coarea chart. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem norm_complex_real_linear_le (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L 1| + |L Complex.I| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hsplit : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hsplit, map_add, map_smul, map_smul]
    _ ≤ ‖z.re • L 1‖ + ‖z.im • L Complex.I‖ := norm_add_le _ _
    _ = |z.re| * |L 1| + |z.im| * |L Complex.I| := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖z‖ * |L 1| + ‖z‖ * |L Complex.I| :=
      add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _))
    _ = (|L 1| + |L Complex.I|) * ‖z‖ := by ring

theorem complex_chart_differential_energy_finite
    {D : Set (ℝ × ℝ)} (hD : IsOpen D) {f : (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f D)
    (henergy : MemLp (FiniteTransfer.planarGradient f) 2 (volume.restrict D)) :
    (∫⁻z in Complex.equivRealProdCLM ⁻¹' D,
      ENNReal.ofReal (‖fderiv ℝ (f ∘ Complex.equivRealProdCLM) z‖ ^ 2)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let μ : Measure ℂ := volume.restrict (e ⁻¹' D)
  have hmp : MeasurePreserving e μ (volume.restrict D) :=
    Complex.volume_preserving_equiv_real_prod.restrict_preimage hD.measurableSet
  have hx := henergy.fst.comp_measurePreserving hmp
  have hy := henergy.snd.comp_measurePreserving hmp
  have hi : Integrable (fun z : ℂ =>
      2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) μ := by
    simpa only [FiniteTransfer.planarGradient, Function.comp_apply, Pi.add_apply] using
      (hx.integrable_sq.add hy.integrable_sq).const_mul 2
  have hfinite : (∫⁻z, ENNReal.ofReal
      (2 * ((fderiv ℝ f (e z)) (1, 0) ^ 2 + (fderiv ℝ f (e z)) (0, 1) ^ 2)) ∂μ) < ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => by positivity)).2 hi |>.lt_top
  apply lt_of_le_of_lt (lintegral_mono_ae ?_) hfinite
  filter_upwards [ae_restrict_mem (hD.preimage e.continuous).measurableSet] with z hz
  apply ENNReal.ofReal_le_ofReal
  have hdiff : DifferentiableAt ℝ f (e z) :=
    (hf.differentiableOn (by norm_num) _ hz).differentiableAt (hD.mem_nhds hz)
  have heq : fderiv ℝ (f ∘ e) z = (fderiv ℝ f (e z)).comp e.toContinuousLinearMap := by
    rw [fderiv_comp z hdiff e.differentiableAt, e.fderiv]
  have hn := norm_complex_real_linear_le ((fderiv ℝ f (e z)).comp e.toContinuousLinearMap)
  have hnorm : ‖fderiv ℝ (f ∘ e) z‖ ≤
      |(fderiv ℝ f (e z)) (1, 0)| + |(fderiv ℝ f (e z)) (0, 1)| := by
    rw [heq]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    e, Complex.equivRealProdCLM_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im] using hn
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [sq_abs ((fderiv ℝ f (e z)) (1, 0)), sq_abs ((fderiv ℝ f (e z)) (0, 1)),
    sq_nonneg (|(fderiv ℝ f (e z)) (1, 0)| - |(fderiv ℝ f (e z)) (0, 1)|)]

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DensityL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real representative of a finite-energy density is locally L² in
the physical planar chart, including densities that are infinite on a null set. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem memLp_two_toReal_of_lintegral_sq_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) (hfinite : (∫⁻x, g x ^ 2 ∂μ) ≠ ∞) :
    MemLp (fun x => (g x).toReal) 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.ennreal_toReal.aestronglyMeasurable).2
  simpa only [ENNReal.toReal_pow] using
    integrable_toReal_of_lintegral_ne_top (hg.pow_const 2).aemeasurable hfinite

attribute [local instance] sphereMetric sphereBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GlobalSphericalDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
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

local instance localInst_r943510_1 : BorelSpace Sphere := ⟨rfl⟩
theorem global_spherical_weighted_density_memLp
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) 2 volume := by
  let k : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hden (z : ℂ) : 0 ≤ 1 / (1 + ‖z‖ ^ 2) := by positivity
  have hc : Continuous (fun z : ℂ => 1 / (1 + ‖z‖ ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_norm.pow 2))
      (fun z => ne_of_gt (by positivity))
  have hk : Measurable k := by
    apply Measurable.mul
    · exact hc.measurable.ennreal_ofReal
    · exact hg.comp OnePoint.continuous_coe.measurable
  have hke : (∫⁻z, k z ^ 2) < ∞ := by
    rw [lintegral_sphericalArea _ (hg.pow_const 2)] at he
    apply lt_of_le_of_lt (lintegral_mono fun z => ?_) he
    dsimp [k]
    rw [mul_pow, ← ENNReal.ofReal_pow (hden z)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl
  have hm := memLp_two_toReal_of_lintegral_sq_ne_top volume hk hke.ne
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  dsimp [k]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hden z)]
  simp only [div_eq_mul_inv, one_mul, mul_comm]

theorem global_spherical_weighted_density_memLp_realProd
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : ℝ × ℝ =>
      (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))
      2 volume := by
  exact (global_spherical_weighted_density_memLp g hg he).comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)

theorem global_spherical_weighted_density_memLp_euclidean
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun x : EuclideanPlane =>
      (g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))
      2 volume := by
  exact (global_spherical_weighted_density_memLp_realProd g hg he).comp_measurePreserving
    euclideanPlaneCoordinates_measurePreserving

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

local instance localInst_r943510_2 : BorelSpace Sphere := ⟨rfl⟩
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

local instance localInst_r943510_3 : BorelSpace Sphere := ⟨rfl⟩
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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalCoordinateCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply weighted coarea to the actual smooth physical representative
of a quotient coordinate. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r943510_4 : BorelSpace Sphere := ⟨rfl⟩
theorem physicalRealCoordinate_ae_finite_weighted_levels
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∀ᵐt ∂volume,
      (∫⁻y in d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
        circleBandGraph d.quotientDomain Q.quotient},
        g y ∂(μH[1] : Measure Sphere)) < ∞ := by
  let e := Complex.equivRealProdCLM
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' FiniteTransfer.realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔
      (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (FiniteTransfer.realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (FiniteTransfer.realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have hf2 : (∫⁻z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  obtain ⟨C, hC, hderiv⟩ := finite_sphere_chart_derivative_decay
  apply ae_finite_spherical_weighted_levels hcoarea hC hderiv hD hf hf2
    (fun t => d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈
      circleBandGraph d.quotientDomain Q.quotient}) _ g hg henergy
  intro t
  ext z
  have hzU (hz : (z : Sphere) ∈ d.physicalDomain) : π z ∈ d.quotientDomain := by
    rw [he ⟨z, hz⟩]
    exact (d.domainEquiv ⟨z, hz⟩).property
  constructor
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t
    rw [Q.pullback z hz]
    exact (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mp ht
  · rintro ⟨hz, ht⟩
    refine ⟨hz, (circleBandGraph_on_open hU Q.quotient_continuous (hzU hz)).mpr ?_⟩
    change (Q.physical (e z) : UnitAddCircle) = t at ht
    rwa [Q.pullback z hz] at ht

theorem physicalRealCoordinate_ae_finite_level_length
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (π : Sphere → X)
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    (Q : PhysicalRealCoordinate d π) :
    ∀ᵐt ∂volume, (μH[1] : Measure Sphere)
      (d.physicalDomain ∩ π ⁻¹' {x | (x, t) ∈ circleBandGraph d.quotientDomain Q.quotient}) < ∞ := by
  have henergy : (∫⁻_ : Sphere, (1 : ℝ≥0∞) ^ 2 ∂sphericalArea) < ∞ := by simp
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π he Q
      (fun _ => 1) measurable_const henergy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalRawCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw barrier compatibility for smooth finite-energy representatives
of the earlier coordinates. The tagged-path inequality and band budget
give compatibility using planar coarea, analytic measurability on finite
tori, and arcs in connected open subsets. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r943510_5 : BorelSpace Sphere := ⟨rfl⟩
theorem raw_barrier_compatibility_with_physical_coordinates
    {X : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {B F : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hBclosure : B ⊆ closure d.quotientDomain)
    (hF : MeasurableSet F) (hFB : F ⊆ B)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (Q i).quotient)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (m : X → ℝ≥0∞) (hm : (∑'x, m x ^ 2) ≠ ∞) (hmF : ∀x ∈ F, m x = 0)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x ∈ d.quotientDomain, u x ∈ Icc 0 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
      liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s)
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain u)
        (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels) = 0 := by
  have htrace := (boundaryTrace_of_ennreal_budget hu hBclosure hm hband).2
  apply raw_barrier_compatibility_of_finite_level_payments hLusin d hU hG hdisj
    π hπ hsurj hfiber he hB hTD hbad hBU hUB hF hFB (hFB.trans hBclosure) harcs
    (fun i => circleBandGraph d.quotientDomain (Q i).quotient)
    (fun i => (isCompact_circleBandGraph (fun x _ => by
      rw [abs_of_nonneg ((Q i).quotient_unit x).1]
      exact ((Q i).quotient_unit x).2)).isClosed)
    (fun i x t => by rw [hlevels]; rfl) g m
    (fun i => physicalRealCoordinate_ae_finite_level_length hcoarea d hU hG π he (Q i))
    (fun i => physicalRealCoordinate_ae_finite_weighted_levels hcoarea d hU hG π he
      (Q i) g hg henergy) hm hmF hweights
    (fun i x => by simpa only [hlevels, mem_preimage, Prod.swap_prod_mk] using hpoint i x)
    ν N u (realBoundaryTrace d.quotientDomain u)
    (fun x hx => by rw [abs_of_nonneg (hu x hx).1]; exact (hu x hx).2)
    hpay (fun x hx => htrace x (hFB hx) (hmF x hx)) n labels hN

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothedBarrierCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatibility of the smoothed coordinate follows from the proved
raw path-cost estimate and pointwise contraction of its dust bands. -/

open Set Function MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r943510_6 : BorelSpace Sphere := ⟨rfl⟩
theorem smoothed_barrier_compatibility_with_physical_coordinates
    {X : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (d : PathCodeData X Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π) (hsurj : Surjective π)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (he : ∀y : d.physicalDomain, π y.val = (d.domainEquiv y).val)
    {B F : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hbad : π '' d.physicalDomainᶜ ⊆ B)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hUB : Disjoint d.quotientDomain B)
    (hBclosure : B ⊆ closure d.quotientDomain)
    (hF : MeasurableSet F) (hFB : F ⊆ B)
    (harcs : ∀C : Set X, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (Q : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (Q i).quotient)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (m : X → ℝ≥0∞) (hm : (∑'x, m x ^ 2) ≠ ∞) (hmF : ∀x ∈ F, m x = 0)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (hpay : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hband : ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
      liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s)
    (v : PhysicalRealCoordinate d π)
    (hcontract : ∀s ∈ B,
      liminf u (𝓝[d.quotientDomain] s) ≤ liminf v.quotient (𝓝[d.quotientDomain] s) ∧
      limsup v.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s))
    (n : ℕ) (labels : Fin (n + 1) → ℕ)
    (hN : (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))
      (N n labels) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))))
      (freeComponentFailure F (circleBandGraph d.quotientDomain v.quotient)
        (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels) = 0 := by
  apply band_contraction_preserves_compatibility
    (volume.prod (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle)))) F
    (circleBandGraph d.quotientDomain v.quotient) (circleBandGraph d.quotientDomain u)
    (fun i => circleBandGraph d.quotientDomain (Q i).quotient) labels
  · intro x hx
    apply circle_band_subset_of_real_band
    apply real_band_subset_of_liminf_limsup d.quotientDomain u v.quotient
      hu v.quotient_unit (hBclosure (hFB hx)) (hcontract x (hFB hx)).1 (hcontract x (hFB hx)).2
  · exact raw_barrier_compatibility_with_physical_coordinates hcoarea hLusin d hU hG hdisj
      π hπ hsurj hfiber he hB hTD hbad hBU hUB hBclosure hF hFB harcs Q hlevels
      g hg henergy m hm hmF hweights hpoint ν N u (fun x _ => hu x) hpay hband n labels hN

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompatibleRealBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.metricBeltramiCoefficient_scalar _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real barrier in the endpoint problem, with its actual physical
representative, countable enlarged flags, and finite-torus compatibility. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

namespace CompatibleRealBarrier

variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
  {previous : ℕ → PhysicalRealCoordinate d π} {flags EStar : Set Sphere}
  {regions : ℕ → Set Sphere} {f : d.quotientDomain → Sphere} {W₁ : Set Sphere}

theorem controlledSize_le_of_partial_bounds
    (B : CompatibleRealBarrier d π previous flags EStar regions f W₁)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀i : Fin 2, eLpNorm (fun x => (fderiv ℝ B.coordinate.physical x)
      (if i = 0 then (1, 0) else (0, 1))) 2
      (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain \
        (fun x : ℝ × ℝ => π (Complex.equivRealProdCLM.symm x : Sphere)) ⁻¹' B.penalty)) ≤ A) :
    B.controlledSize ≤ 2 * A + countingSquareNorm B.weight := by
  refine add_le_add ?_ le_rfl
  have hb := physical_coordinate_gradient_size_le d π B.coordinate
    (fun _ hx => hx.1) hA hbound
  have h := ENNReal.ofReal_le_ofReal hb
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hA] using h

end CompatibleRealBarrier
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

theorem isOpen_region (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen D.region :=
  isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr D.disk
    (fun z hz => (D.level_good z (D.frontier_level hz)).1)

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
-- module Solutions.Q146_CD.CircleDomains_Probability_SphericalDensityNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative global norm bound for the decaying chart density. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem global_spherical_weighted_density_eLpNorm_le
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) 2 volume ≤
      (∫⁻x, g x ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  let F : ℂ → ℝ := fun z => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hF := global_spherical_weighted_density_memLp g hg he
  have hnorm (z : ℂ) : ‖F z‖ₑ ≤ k z := by
    calc
      _ = ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * ENNReal.ofReal (g (z : Sphere)).toReal := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by dsimp [F] <;> positivity),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
        congr 1
        dsimp [F]
        ring
      _ ≤ _ := mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    _ ≤ ∫⁻z : ℂ, k z ^ 2 := lintegral_mono fun z => pow_le_pow_left' (hnorm z) 2
    _ ≤ ∫⁻x, g x ^ 2 ∂sphericalArea := by
      rw [lintegral_sphericalArea _ (hg.pow_const 2)]
      apply lintegral_mono
      intro z
      dsimp [k]
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (1 + ‖z‖ ^ 2))]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LocalizedDensityNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outside the permitted perturbation region, the smoothed barrier is
controlled by the original spherical density, with one fixed chart constant. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem spherical_weighted_density_eLpNorm_euclidean_le
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun x : EuclideanPlane =>
      (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) 2 volume ≤
      (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have hmp : MeasurePreserving complexPlaneCoordinates volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
      euclideanPlaneCoordinates_measurePreserving
  rw [show (fun x : EuclideanPlane =>
      (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) =
    (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) ∘
      complexPlaneCoordinates from rfl]
  rw [eLpNorm_comp_measurePreserving
    (global_spherical_weighted_density_memLp g hg he).aestronglyMeasurable hmp]
  exact global_spherical_weighted_density_eLpNorm_le g hg he

theorem localized_perturbed_density_eLpNorm_le
    {X : Type*} (π : Sphere → X) (O : Set X) (S : Set EuclideanPlane)
    (hS : MeasurableSet S) (hSO : ∀x ∈ S, π (planeSphere x) ∉ O)
    (g g₁ : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (hagree : ∀y, π y ∉ O → g₁ y = g y) (C : ℝ) (hC : 0 ≤ C) :
    eLpNorm (fun x : EuclideanPlane => C *
      ((g₁ (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)))
        2 (volume.restrict S) ≤
      ENNReal.ofReal C * (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have heq : (fun x : EuclideanPlane => C *
      ((g₁ (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) =ᵐ[volume.restrict S]
      (fun x => C * ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [hagree _ (hSO x hx)]
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ eLpNorm (fun x : EuclideanPlane => C *
        ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = ENNReal.ofReal C * eLpNorm (fun x : EuclideanPlane =>
        (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) 2 volume := by
      rw [show (fun x : EuclideanPlane => C *
          ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) =
        C • (fun x : EuclideanPlane =>
          (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) from rfl,
        eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC]
    _ ≤ _ := mul_le_mul' le_rfl (spherical_weighted_density_eLpNorm_euclidean_le g hg he)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalizedRealGradientNorm
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact gradient norm transport on measurable subsets of the physical
chart, used when excluding the permitted penalty region. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_chart_partial_eLpNorm_on
    {D S : Set (ℝ × ℝ)} (hD : IsOpen D) (hS : MeasurableSet S) (hSD : S ⊆ D)
    {w : EuclideanPlane → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanPlaneCoordinates ⁻¹' D))
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S))) :
    eLpNorm (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict S)
      (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (hS.preimage euclideanPlaneCoordinates.continuous.measurable) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  have heq : (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
      (if i = 0 then (1, 0) else (0, 1))) =ᵐ[volume.restrict S]
      (fun p => (fderiv ℝ w (euclideanPlaneCoordinates.symm p)) (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact real_chart_partial_derivative hD hw (hSD hp) i
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_comp_measurePreserving
    (g := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) hi.aestronglyMeasurable hmp


attribute [local instance] sphereMetric sphereBorel

theorem physical_coordinate_partial_eLpNorm_on
    {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (Q : PhysicalRealCoordinate d π) (hQ : Q.quotient = quotientPlaneRepresentative d w)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hSD : S ⊆ FiniteTransfer.realChartDomain d.physicalDomain)
    (i : Fin 2)
    (hi : MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S))) :
    eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2 (volume.restrict S) =
      eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
        2 (volume.restrict (euclideanPlaneCoordinates ⁻¹' S)) := by
  let D := FiniteTransfer.realChartDomain d.physicalDomain
  have hD : IsOpen D := FiniteTransfer.isOpen_realChartDomain hG
  have hq : EqOn Q.physical (w ∘ euclideanPlaneCoordinates.symm) D := by
    intro p hp
    let x := euclideanPlaneCoordinates.symm p
    have hx : x ∈ physicalPlaneDomain d.physicalDomain := by
      change (Complex.equivRealProdCLM.symm p : Sphere) ∈ d.physicalDomain at hp
      change (Complex.equivRealProdCLM.symm (euclideanPlaneCoordinates x) : Sphere) ∈ d.physicalDomain
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
    have hpull := Q.pullback (complexPlaneCoordinates x) hx
    have hpx : Complex.equivRealProdCLM (complexPlaneCoordinates x) = p := by
      simp [complexPlaneCoordinates, x]
    rw [hpx, hQ] at hpull
    exact hpull.trans (quotientPlaneRepresentative_plane d w π he hx)
  have heq : (fun p => (fderiv ℝ Q.physical p) (if i = 0 then (1, 0) else (0, 1)))
      =ᵐ[volume.restrict S] (fun p => (fderiv ℝ (w ∘ euclideanPlaneCoordinates.symm) p)
        (if i = 0 then (1, 0) else (0, 1))) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have hlocal : Q.physical =ᶠ[𝓝 p] w ∘ euclideanPlaneCoordinates.symm := by
      filter_upwards [hD.mem_nhds (hSD hp)] with y hy using hq hy
    rw [hlocal.fderiv_eq]
  rw [eLpNorm_congr_ae heq]
  exact real_chart_partial_eLpNorm_on hD hS hSD hw i hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierPlateauGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact exterior and relatively closed plateau sets used when
smoothing the filled first-arrival barrier. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_compact_plane_exterior_of_nhds
    {V : Set Sphere} (hV : V ∈ 𝓝 OnePoint.infty) :
    ∃K : Set EuclideanPlane, IsCompact K ∧ ∀x ∉ K, planeSphere x ∈ V := by
  obtain ⟨S, ⟨_, hS⟩, hSV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
  refine ⟨complexPlaneCoordinates.symm '' S, hS.image complexPlaneCoordinates.symm.continuous, ?_⟩
  intro x hx
  apply hSV
  left
  refine ⟨complexPlaneCoordinates x, ?_, rfl⟩
  intro hz
  exact hx ⟨complexPlaneCoordinates x, hz, complexPlaneCoordinates.symm_apply_apply x⟩

theorem physical_plateau_relative_complement_open
    {X : Type*} [TopologicalSpace X] {G : Set Sphere} (hG : IsOpen G)
    {π : Sphere → X} (hπ : Continuous π) {A : Set X} (hA : IsClosed A) :
    IsOpen (physicalPlaneDomain G \
      (physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' A)) := by
  have heq : physicalPlaneDomain G \
      (physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' A) =
      physicalPlaneDomain G ∩ (π ∘ planeSphere) ⁻¹' Aᶜ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_compl_iff]
    tauto
  rw [heq]
  exact (isOpen_physicalPlaneDomain hG).inter (hA.isOpen_compl.preimage
    (hπ.comp continuous_planeSphere))

theorem exists_closed_anchor_plateau
    {X : Type*} [TopologicalSpace X] [RegularSpace X]
    {E F : Set X} (hF : IsCompact F) (hFE : F ⊆ interior E) :
    ∃A V : Set X, IsClosed A ∧ IsOpen V ∧ F ⊆ interior A ∧ A ⊆ V ∧ V ⊆ E := by
  obtain ⟨U, hU, hFU, hUE⟩ := hF.exists_isOpen_closure_subset
    (isOpen_interior.mem_nhdsSet.mpr hFE)
  refine ⟨closure U, interior E, isClosed_closure, isOpen_interior, ?_, hUE, interior_subset⟩
  exact hFU.trans (hU.subset_interior_closure)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PotentialRectangleMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local area measurability of the actual bounded barrier follows from
its proved ACL property, using finite simple sampling of good slices. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_7 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_rectangle_aestronglyMeasurable
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere))
      (volume.restrict (Ioo a b ×ˢ Ioo c e)) := by
  obtain ⟨hh, hvv⟩ := potential_rectangle_ACL d hdisj ν N u g hg henergy m hm hpath v hv
    hab.le hce.le hrect
  exact aestronglyMeasurable_on_rectangle_of_ACL _ hab hce hh hvv

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_IncrementDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increment domination passes to derivatives. The integral criterion
then yields the linewise weak-gradient bound used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem abs_derivative_le_of_increment_domination
    {f F : ℝ → ℝ} {x f' F' : ℝ}
    (hf : HasDerivAt f f' x) (hF : HasDerivAt F F' x)
    (h : ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |F y - F x|) : |f'| ≤ |F'| := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope.abs hF.tendsto_slope.abs
  filter_upwards [h.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)

theorem ae_abs_deriv_le_of_integral_bound
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hgnonneg : ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ g x)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      |f x - f y| ≤ ∫t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ g x := by
  have hac : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_of_integral_bound hg (by
      simpa only [uIcc_of_le hab, Real.dist_eq] using hbound)
  have hd := hac.ae_differentiableAt
  have hH := hg.ae_hasDerivAt_integral
  have hi : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff], show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_of_ae hH, hgnonneg, hi] with x hdx hHx hpos hx
  have hdx' : DifferentiableAt ℝ f x := hdx (by simpa only [uIcc_of_le hab] using ⟨hx.1.le, hx.2.le⟩)
  have hHx' := hHx (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))
    a left_mem_uIcc
  have hdom : ∀ᶠ y in 𝓝 x, |f y - f x| ≤
      |(∫t in a..y, g t) - ∫t in a..x, g t| := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    apply (hbound y ⟨hy.1.le, hy.2.le⟩ x ⟨hx.1.le, hx.2.le⟩).trans
    rw [intervalIntegral.integral_interval_sub_left
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show y ∈ Icc a b from ⟨hy.1.le, hy.2.le⟩)))))
      (hg.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
        (uIcc_subset_uIcc left_mem_uIcc (by simpa only [uIcc_of_le hab] using (show x ∈ Icc a b from ⟨hx.1.le, hx.2.le⟩))))),
      intervalIntegral.abs_intervalIntegral_eq]
    simpa only [uIoc_comm x y] using (le_abs_self (∫t in uIoc y x, g t))
  simpa only [abs_of_nonneg hpos] using
    abs_derivative_le_of_increment_domination hdx'.hasDerivAt hHx' hdom

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LineLIntegralDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path inequality is naturally extended-valued. On each finite
slice it bounds the ordinary derivative by the real density. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_abs_deriv_le_of_lintegral_bound
    {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a ≤ b)
    (hg : Measurable g) (hfinite : (∫⁻t in Icc a b, g t) < ∞)
    (hbound : ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      ENNReal.ofReal |f x - f y| ≤ ∫⁻t in uIoc x y, g t) :
    ∀ᵐ x ∂volume.restrict (Icc a b), |deriv f x| ≤ (g x).toReal := by
  have hgint : Integrable (fun t => (g t).toReal) (volume.restrict (Icc a b)) :=
    integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfinite.ne
  apply ae_abs_deriv_le_of_integral_bound hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hgint)
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  intro x hx y hy
  have hsub : uIoc x y ⊆ Icc a b :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hy)
  have hfin : (∫⁻t in uIoc x y, g t) < ∞ :=
    (lintegral_mono_set hsub).trans_lt hfinite
  have hreal : |f x - f y| ≤ (∫⁻t in uIoc x y, g t).toReal := by
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 (hbound x hx y hy)
  rw [integral_toReal hg.aemeasurable (ae_lt_top hg hfin.ne)]
  exact hreal

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialLineDerivativeBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual path-bound potential has the expected derivative estimate
on every physical chart line with finite density integral. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_chart_lintegral_increment_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain) :
    ∀x ∈ Icc a b, ∀y ∈ Icc a b,
      ENNReal.ofReal |v (φ x) - v (φ y)| ≤
        ∫⁻t in uIoc x y, 4 * ((L : ℝ≥0∞) * g (φ t)) := by
  have hseg (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
      ENNReal.ofReal |v (φ y) - v (φ x)| ≤
        ∫⁻t in uIoc x y, 4 * ((L : ℝ≥0∞) * g (φ t)) := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hi := potential_chart_interval_bound d hdisj ν N u g hg m hm hpath v hv
      φ hφ hxy (hL.mono hsub) (fun t ht => hdom (hsub ht))
    rw [uIoc_of_le hxy.le,
      lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    rwa [show (∫⁻t in Ioc x y, g (φ t)) = ∫⁻t in Icc x y, g (φ t) from
      setLIntegral_congr Ioc_ae_eq_Icc]
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · simpa only [abs_sub_comm] using hseg x y hx hy hxy
  · simp
  · simpa only [uIoc_comm y x] using hseg y x hy hx hyx

theorem potential_chart_derivative_bound
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain)
    (hfinite : (∫⁻t in Icc a b, g (φ t)) < ∞) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (v ∘ φ) x| ≤ 4 * ((L : ℝ) * (g (φ x)).toReal) := by
  let ρ : ℝ → ℝ≥0∞ := fun t => 4 * ((L : ℝ≥0∞) * g (φ t))
  have hρ : Measurable ρ := measurable_const.mul (measurable_const.mul (hg.comp hφ))
  have hfin : (∫⁻t in Icc a b, ρ t) < ∞ := by
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)
  have hi := ae_abs_deriv_le_of_lintegral_bound hab hρ hfin
    (potential_chart_lintegral_increment_bound d hdisj ν N u g hg m hm hpath v hv φ hφ hL hdom)
  simpa only [ρ, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
    Function.comp_def] using hi

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MeasurableLineDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On an open set, almost everywhere line differentiability of a measurable
function makes its line derivative measurable. The proof uses actual
difference quotients of the zero extension, so no continuity across the
exceptional lines is required. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddRightInvariant μ]

/-- A Borel representative agrees with the line derivative at every
differentiability point outside one fixed null set. This implication form
can be sliced by Fubini before asserting almost everywhere differentiability. -/
theorem exists_measurable_lineDeriv_representative
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (v : E)
    (hf : AEStronglyMeasurable f (μ.restrict U)) :
    ∃ G : E → ℝ, Measurable G ∧
      ∀ᵐ x ∂μ, x ∈ U → LineDifferentiableAt ℝ f x v →
        G x = lineDeriv ℝ f x v := by
  let F : E → ℝ := U.indicator f
  have hF : AEStronglyMeasurable F μ :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).2 hf
  let F₀ := hF.mk F
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → E → ℝ := fun n x => (h n)⁻¹ * (F₀ (x + h n • v) - F₀ x)
  have hq (n : ℕ) : Measurable (q n) :=
    ((hF.measurable_mk.comp (continuous_id.add continuous_const).measurable).sub
      hF.measurable_mk).const_mul _
  refine ⟨fun x => limsup (fun n => q n x) atTop, Measurable.limsup hq, ?_⟩
  have he (n : ℕ) : ∀ᵐ x ∂μ, F (x + h n • v) = F₀ (x + h n • v) :=
    (measurePreserving_add_right μ (h n • v)).quasiMeasurePreserving.ae hF.ae_eq_mk
  filter_upwards [hF.ae_eq_mk, ae_all_iff.2 he] with x hx₀ hx₁ hx hd
  have hx₀' : F x = F₀ x := hx₀
  have hh : Tendsto h atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => by
        change 1 / ((n : ℝ) + 1) ≠ 0
        positivity)⟩
  have hlim := hd.hasDerivAt.tendsto_slope_zero.comp hh
  have hin : ∀ᶠ n in atTop, x + h n • v ∈ U := by
    have ht : Tendsto (fun n => x + h n • v) atTop (𝓝 x) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add ((tendsto_nhds_of_tendsto_nhdsWithin hh).smul_const v)
    exact ht (hU.mem_nhds hx)
  have hq_lim : Tendsto (fun n => q n x) atTop (𝓝 (lineDeriv ℝ f x v)) := by
    apply hlim.congr'
    filter_upwards [hin] with n hn
    simp only [q, ← hx₀', ← hx₁ n, F, indicator_of_mem hn,
      indicator_of_mem hx, zero_add, zero_smul, add_zero, smul_eq_mul, Function.comp_apply]
  exact hq_lim.limsup_eq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleDerivativeRepresentatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable representatives of the two ACL derivatives in a physical
rectangle. The null set is chosen before slicing, and exceptional lines
are discarded only after applying Fubini. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem ae_mem_Ioo_of_Icc (a b : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩

theorem lineDeriv_horizontal (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (1, 0) = deriv (fun t => f (t, p.2)) p.1 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (t, y)) x 0

theorem lineDeriv_vertical (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (0, 1) = deriv (fun t => f (p.1, t)) p.2 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (x, t)) y 0

theorem exists_measurable_horizontal_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
        G (x, y) = deriv (fun t => f (t, y)) x := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (1, 0) hf
  have hrep' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (1, 0) →
        G (x, y) = lineDeriv ℝ f (x, y) (1, 0) := by
    have hr := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae (by
        simpa only [Measure.volume_eq_prod] using hrep)
    exact Measure.ae_ae_of_ae_prod hr
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc c d, ae_restrict_of_ae hrep'] with y hy hyI hyr
  filter_upwards [ae_mem_Ioo_of_Icc a b,
    ae_restrict_of_ae hy.ae_differentiableAt, ae_restrict_of_ae hyr] with x hxI hxd hxr
  have hd := hxd (Icc_subset_uIcc ⟨hxI.1.le, hxI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (1, 0) := by
    have h : HasDerivAt (fun t => f (t, y)) (deriv (fun t => f (t, y)) x) (x + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add x 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hxr ⟨hxI, hyI⟩ hline).trans (lineDeriv_horizontal f (x, y))

theorem exists_measurable_vertical_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
        G (x, y) = deriv (fun t => f (x, t)) y := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (0, 1) hf
  have hrep' : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (0, 1) →
        G (x, y) = lineDeriv ℝ f (x, y) (0, 1) :=
    Measure.ae_ae_of_ae_prod (by simpa only [Measure.volume_eq_prod] using hrep)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc a b, ae_restrict_of_ae hrep'] with x hx hxI hxr
  filter_upwards [ae_mem_Ioo_of_Icc c d,
    ae_restrict_of_ae hx.ae_differentiableAt, ae_restrict_of_ae hxr] with y hyI hyd hyr
  have hd := hyd (Icc_subset_uIcc ⟨hyI.1.le, hyI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (0, 1) := by
    have h : HasDerivAt (fun t => f (x, t)) (deriv (fun t => f (x, t)) y) (y + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add y 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hyr ⟨hxI, hyI⟩ hline).trans (lineDeriv_vertical f (x, y))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ACLWeakDerivatives
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the Borel representatives of ACL derivatives.
This converts the actual slice derivative into a planar weak derivative. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem integral_mul_horizontal_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hrep : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      G (x, y) = deriv (fun t => f (t, y)) x)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  have hcD : Continuous (fun p => (fderiv ℝ φ p) (1, 0)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hcD.bounded_above_of_compact_support (hsupp.fderiv_apply (𝕜 := ℝ) (1, 0))
  obtain ⟨D, hD⟩ := hφ.continuous.bounded_above_of_compact_support hsupp
  have hl : Integrable (fun p => f p * (fderiv ℝ φ p) (1, 0))
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hf.mul_bdd hcD.aestronglyMeasurable (Eventually.of_forall hC)
  have hr : Integrable (fun p => G p * φ p)
      (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hG.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
  have hp (x y : ℝ) : deriv (fun t => φ (t, y)) x = (fderiv ℝ φ (x, y)) (1, 0) := by
    exact ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv
  have hzero (x y : ℝ) (hx : x ∉ Ioo a b) : φ (x, y) = 0 := by
    by_contra hn
    exact hx (hsub (subset_tsupport φ hn)).1
  have hline : ∀ᵐ y ∂volume.restrict (Icc c d),
      (∫x in Icc a b, f (x, y) * (fderiv ℝ φ (x, y)) (1, 0)) =
        -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
    filter_upwards [hac, hrep] with y hy hyr
    have hφline : AbsolutelyContinuousOnInterval (fun x => φ (x, y)) a b :=
      ((hφ.comp (contDiff_id.prodMk contDiff_const)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
    have hi := hy.integral_mul_deriv_eq_deriv_mul hφline
    rw [hzero b y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hzero a y (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), mul_zero, mul_zero, sub_self,
      zero_sub] at hi
    simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hi
    calc
      _ = ∫x in Icc a b, f (x, y) * deriv (fun t => φ (t, y)) x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => congrArg (fun z => f (x, y) * z) (hp x y).symm
      _ = -(∫x in Icc a b, deriv (fun t => f (t, y)) x * φ (x, y)) := hi
      _ = -(∫x in Icc a b, G (x, y) * φ (x, y)) := by
        congr 1
        exact integral_congr_ae (hyr.mono fun x hx => congrArg (fun z => z * φ (x, y)) hx.symm)
  have he : (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d) =
      (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [he] at hl hr ⊢
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr, ← integral_neg]
  exact integral_congr_ae hline

theorem integral_mul_vertical_deriv_eq_neg
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (hcd : c ≤ d)
    (hf : Integrable f (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hG : Integrable G (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hrep : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      G (x, y) = deriv (fun t => f (x, t)) y)
    {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
      -(∫p in Icc a b ×ˢ Icc c d, G p * φ p) := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hswap : MeasurePreserving e
      (volume.restrict (Icc c d ×ˢ Icc a b))
      (volume.restrict (Icc a b ×ˢ Icc c d)) := by
    change MeasurePreserving Prod.swap _ _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict]
    exact Measure.measurePreserving_swap
  have hs : tsupport (φ ∘ e) ⊆ Ioo c d ×ˢ Ioo a b := by
    change tsupport (φ ∘ e.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage φ e.toHomeomorph]
    intro p hp
    exact ⟨(hsub hp).2, (hsub hp).1⟩
  have hi := integral_mul_horizontal_deriv_eq_neg hcd
    (hswap.integrable_comp_of_integrable hf) (hswap.integrable_comp_of_integrable hG)
    hac hrep (hφ.comp e.contDiff) (hsupp.comp_homeomorph e.toHomeomorph) hs
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ (φ ∘ e) p) (1, 0) = (fderiv ℝ φ (e p)) (0, 1) := by
    rw [fderiv_comp p (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt e.differentiableAt,
      e.fderiv]
    rfl
  simp only [Function.comp_apply, hd] at hi
  calc
    _ = ∫p in Icc c d ×ˢ Icc a b, f (e p) * (fderiv ℝ φ (e p)) (0, 1) :=
      (hswap.integral_comp e.toHomeomorph.measurableEmbedding _).symm
    _ = -(∫p in Icc c d ×ˢ Icc a b, G (e p) * φ (e p)) := hi
    _ = _ := congrArg Neg.neg (hswap.integral_comp e.toHomeomorph.measurableEmbedding
      (fun p => G p * φ p))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RectangleSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! ACL and an L² bound on the line derivatives produce an actual local
Sobolev gradient. All gradient fields here are constructed Borel functions. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem rectangle_restrict_Ioo_eq_Icc (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) =
      volume.restrict (Icc a b ×ˢ Icc c d) := by
  rw [Measure.volume_eq_prod]
  exact Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

theorem exists_rectangle_weak_gradient
    {f ρ : ℝ × ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hρ : Measurable ρ) (hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hacx : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b)
    (hacy : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d)
    (hbx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y))
    (hby : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y)) :
    ∃ Gx Gy : ℝ × ℝ → ℝ, Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p ∧ |Gy p| ≤ ρ p) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p) := by
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c d)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)) := by
    rw [rectangle_restrict_Ioo_eq_Icc]
    exact hf.aestronglyMeasurable
  obtain ⟨Gx, hGx, hrx⟩ := exists_measurable_horizontal_derivative f hfmeas hacx
  obtain ⟨Gy, hGy, hry⟩ := exists_measurable_vertical_derivative f hfmeas hacy
  have hx : ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
      |Gx (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hrx, hbx] with y hy hb
    filter_upwards [hy, hb] with x hx hb
    simpa only [hx] using hb
  have hy : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
      |Gy (x, y)| ≤ ρ (x, y) := by
    filter_upwards [hry, hby] with x hx hb
    filter_upwards [hx, hb] with y hy hb
    simpa only [hy] using hb
  have hmeasx : MeasurableSet {p : ℝ × ℝ | |Gx p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGx.norm hρ
  have hmeasy : MeasurableSet {p : ℝ × ℝ | |Gy p| ≤ ρ p} :=
    by simpa only [Real.norm_eq_abs] using measurableSet_le hGy.norm hρ
  have hBx : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gx p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasx).2 ((Measure.ae_ae_comm hmeasx).2 hx)
  have hBy : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), |Gy p| ≤ ρ p := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (Measure.ae_prod_iff_ae_ae hmeasy).2 hy
  have hx₂ : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGx.aestronglyMeasurable (hBx.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  have hy₂ : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)) :=
    hρ₂.of_le hGy.aestronglyMeasurable (hBy.mono fun p hp => by
      simpa only [Real.norm_eq_abs] using hp.trans (le_abs_self _))
  refine ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hBx.and hBy, ?_⟩
  intro φ hφ hs hsub
  exact ⟨integral_mul_horizontal_deriv_eq_neg hab (hf.integrable (by norm_num))
    (hx₂.integrable (by norm_num)) hacx hrx hφ hs hsub,
    integral_mul_vertical_deriv_eq_neg hcd (hf.integrable (by norm_num))
    (hy₂.integrable (by norm_num)) hacy hry hφ hs hsub⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_PotentialPrescribedChartBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barrier derivatives on almost every horizontal and vertical
slice satisfy a common local bound by the physical density. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_8 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_rectangle_derivative_bounds_with_constant
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain)
    (L : ℝ≥0) (hL : LipschitzOnWith L ((↑) : ℂ → Sphere)
      (closedComplexRectangle a b c e)) :
      (∀ᵐ y ∂volume.restrict (Icc c e), ∀ᵐ x ∂volume.restrict (Icc a b),
        |deriv (fun t => v ((⟨t, y⟩ : ℂ) : Sphere)) x| ≤
          4 * ((L : ℝ) * (g ((⟨x, y⟩ : ℂ) : Sphere)).toReal)) ∧
      (∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c e),
        |deriv (fun t => v ((⟨x, t⟩ : ℂ) : Sphere)) y| ≤
          4 * ((L : ℝ) * (g ((⟨x, y⟩ : ℂ) : Sphere)).toReal)) := by
  let K := closedComplexRectangle a b c e
  have hK : IsCompact K := isCompact_closedComplexRectangle a b c e
  obtain ⟨hh, hvv⟩ := ae_finite_planar_density_slices g hg henergy hK
  constructor
  · filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_Icc] with y hy hyI
    let φ : ℝ → Sphere := fun x => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨t, y⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc a b) := by
      intro x hx x' hx'
      have h := hL (mk_mem_closedComplexRectangle hx hyI) (mk_mem_closedComplexRectangle hx' hyI)
      simpa only [Complex.edist_of_im_eq (show (⟨x, y⟩ : ℂ).im = (⟨x', y⟩ : ℂ).im from rfl)] using h
    have hfin : (∫⁻x in Icc a b, g (φ x)) < ∞ := by
      have he : (∫⁻x in Icc a b, g (φ x)) =
          ∫⁻x in Icc a b, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hx hyI)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hy
    simpa only [Function.comp_def] using potential_chart_derivative_bound d hdisj ν N u g hg m hm hpath
      v hv φ hφ hab hLip (fun x hx => hrect _ (mk_mem_closedComplexRectangle hx hyI)) hfin
  · filter_upwards [ae_restrict_of_ae hvv, ae_restrict_mem measurableSet_Icc] with x hx hxI
    let φ : ℝ → Sphere := fun y => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨x, t⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc c e) := by
      intro y hy y' hy'
      have h := hL (mk_mem_closedComplexRectangle hxI hy) (mk_mem_closedComplexRectangle hxI hy')
      simpa only [Complex.edist_of_re_eq (show (⟨x, y⟩ : ℂ).re = (⟨x, y'⟩ : ℂ).re from rfl)] using h
    have hfin : (∫⁻y in Icc c e, g (φ y)) < ∞ := by
      have he : (∫⁻y in Icc c e, g (φ y)) =
          ∫⁻y in Icc c e, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro y hy
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hxI hy)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hx
    simpa only [Function.comp_def] using potential_chart_derivative_bound d hdisj ν N u g hg m hm hpath
      v hv φ hφ hce hLip (fun y hy => hrect _ (mk_mem_closedComplexRectangle hxI hy)) hfin

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PotentialWeightedSobolev
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bounded first-arrival potential has a local L² weak gradient
on each physical rectangle. No Sobolev regularity is added as an input. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_9 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_rectangle_weighted_weak_gradient
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain)
    (L : ℝ≥0) (hL : LipschitzOnWith L ((↑) : ℂ → Sphere)
      (closedComplexRectangle a b c e))
    (C : ℝ) (hLC : ∀z ∈ closedComplexRectangle a b c e,
      (L : ℝ) ≤ C / (1 + ‖z‖ ^ 2)) :
    let f : ℝ × ℝ → ℝ := fun p => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)
    MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
    ∃ (Gx Gy : ℝ × ℝ → ℝ), Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c e),
        |Gx p| ≤ 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2)) ∧
        |Gy p| ≤ 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c e →
        (∫p in Icc a b ×ˢ Icc c e, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c e, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c e, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c e, Gy p * φ p) := by
  let f : ℝ × ℝ → ℝ := fun p => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c e)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Icc a b ×ˢ Icc c e)) := by
    rw [← rectangle_restrict_Ioo_eq_Icc]
    exact potential_rectangle_aestronglyMeasurable d hdisj ν N u g hg henergy m hm hpath
      v hv hab hce hrect
  have hfunit : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c e), f p ∈ Icc 0 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    dsimp [f]
    rw [hv _ (hrect _ (mk_mem_closedComplexRectangle hp.1 hp.2))]
    exact hu _
  have hf₂ : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c e)) :=
    memLp_of_bounded hfunit hfmeas 2
  obtain ⟨hacx, hacy⟩ := potential_rectangle_ACL d hdisj ν N u g hg henergy m hm hpath
    v hv hab.le hce.le hrect
  obtain ⟨hbx, hby⟩ := potential_rectangle_derivative_bounds_with_constant
    d hdisj ν N u g hg henergy m hm hpath v hv hab.le hce.le hrect L hL
  let ρ : ℝ × ℝ → ℝ := fun p => 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))
  have hρ : Measurable ρ := by
    have hmap : Measurable (fun p : ℝ × ℝ => ((⟨p.1, p.2⟩ : ℂ) : Sphere)) :=
      OnePoint.continuous_coe.measurable.comp Complex.measurableEquivRealProd.symm.measurable
    have hc : Continuous (fun p : ℝ × ℝ => 1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2) :=
      continuous_const.add ((Complex.equivRealProdCLM.symm.continuous.norm).pow 2)
    exact measurable_const.mul ((hg.comp hmap).ennreal_toReal.div hc.measurable)
  have hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c e)) :=
    ((global_spherical_weighted_density_memLp_realProd g hg henergy).const_mul
      (4 * C)).restrict _
  have hb (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc c e) :
      4 * ((L : ℝ) * (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal) ≤ ρ p := by
    have hh := mul_le_mul_of_nonneg_right
      (hLC _ (mk_mem_closedComplexRectangle hp.1 hp.2))
      (ENNReal.toReal_nonneg (a := g ((⟨p.1, p.2⟩ : ℂ) : Sphere)))
    dsimp [ρ]
    calc
      _ ≤ 4 * (C / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2) *
          (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hbx' : ∀ᵐ y ∂volume.restrict (Icc c e), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y) := by
    filter_upwards [hbx, ae_restrict_mem measurableSet_Icc] with y hy hyI
    filter_upwards [hy, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact hx.trans (hb (x, y) ⟨hxI, hyI⟩)
  have hby' : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c e),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y) := by
    filter_upwards [hby, ae_restrict_mem measurableSet_Icc] with x hx hxI
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with y hy hyI
    exact hy.trans (hb (x, y) ⟨hxI, hyI⟩)
  obtain ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hbound, hweak⟩ :=
    exists_rectangle_weak_gradient hab.le hce.le hf₂ hρ hρ₂ hacx hacy hbx' hby'
  exact ⟨hf₂, Gx, Gy, hGx, hGy, hx₂, hy₂, hbound, hweak⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PlanarSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual planar weak derivative identities to the
Euclidean coordinates of the repository's Sobolev approximation library. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem weakPartial_of_planar_identity
    {f G : ℝ × ℝ → ℝ} {a b c d : ℝ} (i : Fin 2) (v : ℝ × ℝ)
    (hv : euclideanPlaneCoordinates (EuclideanSpace.single i 1) = v)
    (hweak : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ ψ p) v) =
        -(∫p in Icc a b ×ˢ Icc c d, G p * ψ p)) :
    DeGiorgi.HasWeakPartialDeriv i (G ∘ euclideanPlaneCoordinates)
      (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)) := by
  intro φ hφ hs hsub
  let e := euclideanPlaneCoordinates
  change (∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d),
    f (e x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
      -(∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), G (e x) * φ x)
  change e (EuclideanSpace.single i 1) = v at hv
  let ψ : ℝ × ℝ → ℝ := φ ∘ e.symm
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.symm.contDiff
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph e.symm.toHomeomorph
  have hsubψ : tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d := by
    change tsupport (φ ∘ e.symm.toHomeomorph) ⊆ _
    rw [tsupport_comp_eq_preimage]
    intro p hp
    have hh := hsub hp
    change e (e.symm p) ∈ Ioo a b ×ˢ Ioo c d at hh
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (p : ℝ × ℝ) :
      (fderiv ℝ ψ p) v = (fderiv ℝ φ (e.symm p)) (EuclideanSpace.single i 1) := by
    rw [fderiv_comp p (hφ.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
      e.symm.fderiv]
    change (fderiv ℝ φ (e.symm p)) (e.symm v) = _
    rw [← hv, ContinuousLinearEquiv.symm_apply_apply]
  have hp := hweak ψ hψ hsψ hsubψ
  rw [← rectangle_restrict_Ioo_eq_Icc] at hp
  have hmp : MeasurePreserving e (volume.restrict (e ⁻¹' (Ioo a b ×ˢ Ioo c d)))
      (volume.restrict (Ioo a b ×ˢ Ioo c d)) :=
    euclideanPlaneCoordinates_measurePreserving.restrict_preimage
      (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  calc
    _ = ∫x in e ⁻¹' (Ioo a b ×ˢ Ioo c d), f (e x) * (fderiv ℝ ψ (e x)) v := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [hd,
        ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫p in Ioo a b ×ˢ Ioo c d, f p * (fderiv ℝ ψ p) v :=
      hmp.integral_comp e.toHomeomorph.measurableEmbedding
        (fun p => f p * (fderiv ℝ ψ p) v)
    _ = -(∫p in Ioo a b ×ˢ Ioo c d, G p * ψ p) := hp
    _ = _ := by
      rw [← hmp.integral_comp e.toHomeomorph.measurableEmbedding (fun p => G p * ψ p)]
      simp only [ψ, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve a common pointwise derivative bound when transporting rectangle
weak derivatives into the Euclidean Sobolev witness. -/

open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem exists_bounded_rectangle_sobolev_witness
    {f Gx Gy r : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hf : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hx : MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hy : MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c d)))
    (hbound : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d),
      |Gx p| ≤ r p ∧ |Gy p| ≤ r p)
    (hweak : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b ×ˢ Ioo c d →
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (1, 0)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gx p * φ p) ∧
      (∫p in Icc a b ×ˢ Icc c d, f p * (fderiv ℝ φ p) (0, 1)) =
        -(∫p in Icc a b ×ˢ Icc c d, Gy p * φ p)) :
    ∃H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c d)),
        |H.weakGrad x i| ≤ r (euclideanPlaneCoordinates x) := by
  let W := Ioo a b ×ˢ Ioo c d
  have hmp := euclideanPlaneCoordinates_measurePreserving.restrict_preimage (s := W)
    (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  have hf' : MemLp f 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hx' : MemLp Gx 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hy' : MemLp Gy 2 (volume.restrict W) := by rwa [rectangle_restrict_Ioo_eq_Icc]
  have hb' : ∀ᵐ p ∂volume.restrict W, |Gx p| ≤ r p ∧ |Gy p| ≤ r p := by
    rwa [rectangle_restrict_Ioo_eq_Icc]
  let G : EuclideanPlane → EuclideanPlane := fun x =>
    WithLp.toLp 2 fun i => if i = 0 then Gx (euclideanPlaneCoordinates x)
      else Gy (euclideanPlaneCoordinates x)
  let H : DeGiorgi.MemW1pWitness 2 (f ∘ euclideanPlaneCoordinates)
      (euclideanPlaneCoordinates ⁻¹' W) := {
    memLp := hf'.comp_measurePreserving hmp
    weakGrad := G
    weakGrad_component_memLp := by
      intro i
      fin_cases i
      · exact hx'.comp_measurePreserving hmp
      · exact hy'.comp_measurePreserving hmp
    isWeakGrad := by
      intro i
      fin_cases i
      · exact weakPartial_of_planar_identity 0 (1, 0) euclideanPlaneCoordinates_single_zero
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).1)
      · exact weakPartial_of_planar_identity 1 (0, 1) euclideanPlaneCoordinates_single_one
          (fun φ hφ hs hsub => (hweak φ hφ hs hsub).2) }
  refine ⟨H, ?_⟩
  intro i
  have hb := hmp.quasiMeasurePreserving.ae hb'
  filter_upwards [hb] with x hx
  fin_cases i
  · exact hx.1
  · exact hx.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PotentialWeightedWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local Sobolev witnesses with a single decaying global density bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_10 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_small_rectangle_sobolev_witness
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hdiam : ∀x ∈ closedComplexRectangle a b c e,
      ∀y ∈ closedComplexRectangle a b c e, dist x y ≤ 1) :
    ∃H : DeGiorgi.MemW1pWitness 2
        ((fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)),
        |H.weakGrad x i| ≤ 4 * (9 * C) *
          ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)) := by
  have hconv : Convex ℝ (closedComplexRectangle a b c e) :=
    ((convex_Icc a b).prod (convex_Icc c e)).linear_image
      Complex.equivRealProdCLM.symm.toLinearMap
  have hne : (closedComplexRectangle a b c e).Nonempty :=
    ⟨⟨a, c⟩, mk_mem_closedComplexRectangle ⟨le_rfl, hab.le⟩ ⟨le_rfl, hce.le⟩⟩
  obtain ⟨L, hL, hLC⟩ := finite_sphere_chart_lipschitz_on_small_convex hC hderiv hconv hne hdiam
  obtain ⟨hf, Gx, Gy, _, _, hx, hy, hb, hw⟩ :=
    potential_rectangle_weighted_weak_gradient d hdisj ν N u hu g hg henergy m hm hpath v hv
      hab hce hrect L hL (9 * C) hLC
  obtain ⟨H, hH⟩ := exists_bounded_rectangle_sobolev_witness hf hx hy hb hw
  exact ⟨H, hH⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalizedPartitionEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localizing the global smoothing error keeps the original density on
the complement of a penalty region. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem partition_smooth_gradient_energy_on
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (hW : ∀j, MeasurableSet (W j)) (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (G : ι → EuclideanPlane → ℝ)
    (hGm : ∀j, AEStronglyMeasurable (G j) (volume.restrict (W j)))
    (g : EuclideanPlane → ℝ)
    (hG : ∀j, ∀ᵐx ∂volume.restrict (W j), |G j x| ≤ g x)
    {w : EuclideanPlane → ℝ} (i : Fin 2) {ε : ℝ≥0∞}
    (herr : eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1) -
      ∑ᶠj, ρ.weight j x * G j x) 2 (volume.restrict Ω) < ε)
    (S : Set EuclideanPlane) (hS : S ⊆ Ω) :
    eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
      ε + eLpNorm g 2 (volume.restrict S) := by
  let P : EuclideanPlane → ℝ := fun x => ∑ᶠj, ρ.weight j x * G j x
  let D : EuclideanPlane → ℝ := fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)
  have hμ : volume.restrict S ≤ volume.restrict (Ω : Set EuclideanPlane) :=
    Measure.restrict_mono_set volume hS
  have hP : AEStronglyMeasurable P (volume.restrict S) :=
    (partition_component_aestronglyMeasurable ρ W hW hsub G hGm).mono_measure
      Measure.restrict_le_self
  have hnormP : eLpNorm P 2 (volume.restrict S) ≤ eLpNorm g 2 (volume.restrict S) := by
    apply eLpNorm_mono_ae_real
    exact (ae_mono hμ) (partition_component_bound ρ W hW hsub G g hG)
  calc
    _ = eLpNorm (fun x => (D x - P x) + P x) 2 (volume.restrict S) := by
      congr 1
      funext x
      exact (sub_add_cancel _ _).symm
    _ ≤ eLpNorm (fun x => D x - P x) 2 (volume.restrict S) +
        eLpNorm P 2 (volume.restrict S) := eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
    _ ≤ ε + eLpNorm g 2 (volume.restrict S) := add_le_add
      ((eLpNorm_mono_measure _ hμ).trans herr.le) hnormP

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalizedPotentialSmoothing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive smoothing with a localized energy estimate, retaining the global finite-energy assertion. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_11 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_positive_partition_smoothing_with_local_energy
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (a b c e : ι → ℝ)
    (hab : ∀j, a j < b j) (hce : ∀j, c j < e j)
    (hrect : ∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      (z : Sphere) ∈ d.physicalDomain)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)))
    (hdiam : ∀j x, x ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      ∀y ∈ closedComplexRectangle (a j) (b j) (c j) (e j), dist x y ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (S : Set EuclideanPlane) (hS : S ⊆ Ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let f : EuclideanPlane → ℝ :=
      (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
    let W : ι → Set EuclideanPlane := fun j =>
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
    ∃w : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ (∀x ∈ Ω, w x ∈ Icc 0 1) ∧
      (∀x ∈ Ω, ∀r s : ℝ,
        (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, f y ∈ Icc r s) → w x ∈ Icc r s) ∧
      ∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S) := by
  let f : EuclideanPlane → ℝ :=
    (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hlocal (j : ι) : ∃H : DeGiorgi.MemW1pWitness 2 f (W j),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict (W j), |H.weakGrad x i| ≤ 4 * (9 * C) *
        ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)) :=
    potential_small_rectangle_sobolev_witness d hdisj ν N u hu g hg henergy m hm hpath v hv
      (hab j) (hce j) (hrect j) C hC hderiv (hdiam j)
  choose H hH using hlocal
  have hfunit (j : ι) (x : EuclideanPlane) (hx : x ∈ W j) : f x ∈ Icc 0 1 := by
    have hp : euclideanPlaneCoordinates x ∈ Ioo (a j) (b j) ×ˢ Ioo (c j) (e j) := hx
    have hphys := hrect j _ (mk_mem_closedComplexRectangle
      ⟨hp.1.1.le, hp.1.2.le⟩ ⟨hp.2.1.le, hp.2.2.le⟩)
    change v ((⟨(euclideanPlaneCoordinates x).1,
      (euclideanPlaneCoordinates x).2⟩ : ℂ) : Sphere) ∈ Icc 0 1
    rw [hv _ hphys]
    exact hu _
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨w, hs, hunit, hinterval, herr⟩ :=
    exists_positive_partition_smoothing ρ W hW hsub f H hfunit δ hδ
  refine ⟨w, hs, hunit, hinterval, ?_⟩
  intro i
  have hdensity := (global_spherical_weighted_density_memLp_euclidean g hg henergy).const_mul
    (4 * (9 * C))
  have hEn := partition_smooth_gradient_energy ρ W (fun j => (hW j).measurableSet) hsub
    (fun j x => (H j).weakGrad x i)
    (fun j => (H j).weakGrad_component_memLp i |>.aestronglyMeasurable)
    (hdensity.restrict Ω) (fun j => hH j i) i ((herr i).trans_lt hsum)
  refine ⟨hEn.1, hEn.2.trans (add_le_add le_rfl
    (eLpNorm_mono_measure _ Measure.restrict_le_self)), ?_⟩
  exact partition_smooth_gradient_energy_on ρ W (fun j => (hW j).measurableSet) hsub
    (fun j x => (H j).weakGrad x i)
    (fun j => (H j).weakGrad_component_memLp i |>.aestronglyMeasurable)
    _ (fun j => hH j i) i ((herr i).trans_lt hsum) S hS

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientFinitePlane
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite physical chart covers the quotient away from the image of infinity. -/

open Set Function
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem quotient_injOn_physical_domain
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val) :
    InjOn π d.physicalDomain := by
  intro x hx y hy hxy
  have h : d.domainEquiv ⟨x, hx⟩ = d.domainEquiv ⟨y, hy⟩ := by
    apply Subtype.ext
    simpa only [he] using hxy
  exact congrArg Subtype.val (d.domainEquiv.injective h)

theorem quotient_finite_plane_mapsTo
    (d : PathCodeData X Sphere) (π : Sphere → X)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) :
    MapsTo (π ∘ planeSphere) (physicalPlaneDomain d.physicalDomain)
      (d.quotientDomain \ {π OnePoint.infty}) := by
  intro x hx
  have hp : planeSphere x ∈ d.physicalDomain := hx
  constructor
  · change π (planeSphere x) ∈ d.quotientDomain
    rw [← he ⟨planeSphere x, hp⟩]
    exact (d.domainEquiv ⟨planeSphere x, hp⟩).property
  · intro hh
    have heq := quotient_injOn_physical_domain d π he hp hinf hh
    exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) heq

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PatchBandPreservation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive partition sums preserve every boundary band when all active
sampling patches shrink towards that boundary point. -/

open Set Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X ι : Type*}

section Topological
variable [TopologicalSpace X]

theorem band_inclusion_of_eventual_interval_preservation
    (G : Set X) (u v : X → ℝ) {s : X} (hGs : s ∈ closure G)
    (hb : ∀x, u x ∈ Icc 0 1)
    (htransfer : ∀a b : ℝ, (∀ᶠ y in 𝓝[G] s, u y ∈ Icc a b) →
      ∀ᶠ x in 𝓝[G] s, v x ∈ Icc a b) :
    liminf u (𝓝[G] s) ≤ liminf v (𝓝[G] s) ∧
      limsup v (𝓝[G] s) ≤ limsup u (𝓝[G] s) := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hGs
  have hv := htransfer 0 1 (Eventually.of_forall hb)
  have hul : IsBoundedUnder (· ≥ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x => (hb x).1)
  have huu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun x => (hb x).2)
  have hvl : IsBoundedUnder (· ≥ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_ge (hv.mono fun _ h => h.1)
  have hvu : IsBoundedUnder (· ≤ ·) (𝓝[G] s) v :=
    isBoundedUnder_of_eventually_le (hv.mono fun _ h => h.2)
  constructor
  · apply (le_liminf_iff' hvu.isCoboundedUnder_ge hvl).2
    intro a ha
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc a 1 := by
      filter_upwards [eventually_lt_of_lt_liminf ha hul] with y hy
      exact ⟨hy.le, (hb y).2⟩
    exact (htransfer a 1 he).mono fun _ h => h.1
  · apply (limsup_le_iff' hvl.isCoboundedUnder_le hvu).2
    intro b hb'
    have he : ∀ᶠ y in 𝓝[G] s, u y ∈ Icc 0 b := by
      filter_upwards [eventually_lt_of_limsup_lt hb' huu] with y hy
      exact ⟨(hb y).1, hy.le⟩
    exact (htransfer 0 b he).mono fun _ h => h.2

end Topological

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientSamplingBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking physical sampling patches preserve bands in the quotient
space, without requiring continuity of the boundary extension. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X ι : Type*} [MetricSpace X]

theorem quotient_sampling_eventual_bounds
    (Ω : Set EuclideanPlane) (U B : Set X) (q : EuclideanPlane → X)
    (weight : ι → EuclideanPlane → ℝ) (W : ι → Set EuclideanPlane)
    (u v : X → ℝ) (w : EuclideanPlane → ℝ)
    (hq : MapsTo q Ω U) (hcover : U ⊆ q '' Ω)
    (hvalue : ∀x ∈ Ω, v (q x) = w x)
    (hW : ∀j, W j ⊆ Ω)
    (hclose : ∀x ∈ Ω, ∀j, weight j x ≠ 0 → ∀y ∈ W j,
      dist (q y) (q x) ≤ infDist (q x) B)
    (hpreserve : ∀x ∈ Ω, ∀a b : ℝ,
      (∀j, weight j x ≠ 0 → ∀y ∈ W j, u (q y) ∈ Icc a b) → w x ∈ Icc a b)
    {s : X} (hs : s ∈ B) {a b : ℝ}
    (hu : ∀ᶠ y in 𝓝[U] s, u y ∈ Icc a b) :
    ∀ᶠ y in 𝓝[U] s, v y ∈ Icc a b := by
  obtain ⟨V, hV, hVU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hnear : ∀ᶠ z in 𝓝[U] s, dist z s < ε / 2 :=
    nhdsWithin_le_nhds (ball_mem_nhds s (half_pos hε))
  filter_upwards [self_mem_nhdsWithin, hnear] with z hz hzs
  obtain ⟨x, hx, rfl⟩ := hcover hz
  rw [hvalue x hx]
  apply hpreserve x hx a b
  intro j hj y hy
  apply hVU
  refine ⟨hball ?_, hq (hW j hy)⟩
  change dist (q y) s < ε
  have hdist := hclose x hx j hj y hy
  have hi : infDist (q x) B ≤ dist (q x) s := infDist_le_dist_of_mem hs
  linarith [dist_triangle (q y) (q x) s]

theorem quotient_sampling_band_inclusion
    (Ω : Set EuclideanPlane) (U B : Set X) (q : EuclideanPlane → X)
    (weight : ι → EuclideanPlane → ℝ) (W : ι → Set EuclideanPlane)
    (u v : X → ℝ) (w : EuclideanPlane → ℝ)
    (hq : MapsTo q Ω U) (hcover : U ⊆ q '' Ω)
    (hvalue : ∀x ∈ Ω, v (q x) = w x)
    (hW : ∀j, W j ⊆ Ω)
    (hclose : ∀x ∈ Ω, ∀j, weight j x ≠ 0 → ∀y ∈ W j,
      dist (q y) (q x) ≤ infDist (q x) B)
    (hpreserve : ∀x ∈ Ω, ∀a b : ℝ,
      (∀j, weight j x ≠ 0 → ∀y ∈ W j, u (q y) ∈ Icc a b) → w x ∈ Icc a b)
    (hu : ∀x, u x ∈ Icc 0 1) {s : X} (hs : s ∈ B) (hUs : s ∈ closure U) :
    liminf u (𝓝[U] s) ≤ liminf v (𝓝[U] s) ∧
      limsup v (𝓝[U] s) ≤ limsup u (𝓝[U] s) := by
  apply band_inclusion_of_eventual_interval_preservation U u v hUs hu
  intro a b hab
  exact quotient_sampling_eventual_bounds Ω U B q weight W u v w
    hq hcover hvalue hW hclose hpreserve hs hab

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PhysicalPartitionBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quotient-band consequence of a physical positive sampling partition. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem physical_partition_band_inclusion
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    {ι : Type*} (ρ : OpenPlanePartition (physicalPlaneOpens d.physicalDomain hG) ι)
    (a b c e : ι → ℝ)
    (hphys : ∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      (z : Sphere) ∈ d.physicalDomain)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)))
    (hpair : ∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) →
      ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)),
        dist (π (planeSphere y)) (π (planeSphere x)) ≤ Metric.infDist (π (planeSphere x)) d.dust)
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (w : EuclideanPlane → ℝ)
    (hinter : ∀x ∈ physicalPlaneDomain d.physicalDomain, ∀r s : ℝ,
      (∀j, ρ.weight j x ≠ 0 → ∀y ∈
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)),
        u (π (planeSphere y)) ∈ Icc r s) → w x ∈ Icc r s) :
    ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
      liminf u (𝓝[d.quotientDomain] s) ≤
        liminf (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ∧
      limsup (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ≤
        limsup u (𝓝[d.quotientDomain] s) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let q : EuclideanPlane → X := π ∘ planeSphere
  intro s hs hscl
  have hsne : s ≠ π OnePoint.infty := by
    intro heq
    exact hinfB (heq ▸ hs)
  let U := d.quotientDomain \ {π OnePoint.infty}
  have hnhds : 𝓝[U] s = 𝓝[d.quotientDomain] s :=
    hsne.nhdsWithin_sdiff_singleton d.quotientDomain
  have hsclU : s ∈ closure U := by
    rw [mem_closure_iff_nhdsWithin_neBot, hnhds]
    exact mem_closure_iff_nhdsWithin_neBot.mp hscl
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hWO (j : ι) : W j ⊆ Ω := by
    intro x hx
    exact hphys j _ (mk_mem_closedComplexRectangle (hclosed j hx).1 (hclosed j hx).2)
  have hbound := quotient_sampling_band_inclusion (Ω : Set EuclideanPlane) U d.dust q
    ρ.weight W u (quotientPlaneRepresentative d w) w
    (quotient_finite_plane_mapsTo d π he hinf) (quotient_finite_plane_covers d π he)
    (fun x hx => quotientPlaneRepresentative_plane d w π he hx) hWO
    (by
      intro x hx j hj y hy
      exact hpair j x (hclosed j (hsub j (subset_tsupport (ρ.weight j) hj))) y (hclosed j hy))
    hinter hu hs hsclU
  simpa only [hnhds] using hbound


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RefinedShrinkingRectanglePartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shrinking rectangle construction can respect specified open sampling neighborhoods. -/

open Set Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem exists_small_shrinking_partition_refining_neighborhoods
    {X : Type*} [MetricSpace X] (Ω : TopologicalSpace.Opens EuclideanPlane)
    (q : EuclideanPlane → X) (hq : ContinuousOn q Ω)
    (B : Set X) (hB : IsClosed B) (hne : B.Nonempty) (hqB : ∀x ∈ Ω, q x ∉ B)
    (N : Ω → Set EuclideanPlane) (hN : ∀x, IsOpen (N x)) (hxN : ∀x : Ω, x.val ∈ N x) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι) (center : ι → Ω)
      (a b c d : ι → ℝ),
      (∀j, a j < b j ∧ c j < d j) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) ⊆ Ω ∩ N (center j)) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (q y) (q x) ≤ Metric.infDist (q x) B) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)),
          dist (⟨x 0, x 1⟩ : ℂ) (⟨y 0, y 1⟩ : ℂ) ≤ 1) := by
  choose a b c d hab hcd hpoint hrect hpair hdiam using
    fun x : Ω => exists_small_closed_coordinate_rectangle_with_diameter
      (Ω.isOpen.inter (hN x)) q (hq.mono inter_subset_left) B hB hne
      (show x.val ∈ (Ω : Set EuclideanPlane) ∩ N x from ⟨x.property, hxN x⟩)
      (hqB x x.property)
  let U : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hU (x : Ω) : U x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hpoint x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω U hU
  refine ⟨ι, hι, ρ, center, a ∘ center, b ∘ center, c ∘ center, d ∘ center,
    fun j => ⟨hab (center j), hcd (center j)⟩, fun j => hrect (center j), ?_, ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := hsub j hx
    exact hy
  · intro j x hx y hy
    exact hpair (center j) y hy x hx

  · intro j x hx y hy
    exact hdiam (center j) x hx y hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RefinedPhysicalSampling
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined sampling for the actual physical quotient, with plateau neighborhoods. -/

open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem exists_refined_physical_sampling_partition
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (N : physicalPlaneOpens d.physicalDomain hG → Set EuclideanPlane)
    (hN : ∀x, IsOpen (N x)) (hxN : ∀x, x.val ∈ N x) :
    ∃ (ι : Type) (_ : Countable ι)
      (ρ : OpenPlanePartition (physicalPlaneOpens d.physicalDomain hG) ι)
      (center : ι → physicalPlaneOpens d.physicalDomain hG) (a b c e : ι → ℝ),
      (∀j, a j < b j ∧ c j < e j) ∧
      (∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
        (z : Sphere) ∈ d.physicalDomain) ∧
      (∀j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))) ∧
      (∀j x, x ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) →
        ∀y ∈ euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)),
          dist (π (planeSphere y)) (π (planeSphere x)) ≤ Metric.infDist (π (planeSphere x)) d.dust) ∧
      (∀j x, x ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
        ∀y ∈ closedComplexRectangle (a j) (b j) (c j) (e j), dist x y ≤ 1) ∧
      (∀j, euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) ⊆ N (center j)) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let q : EuclideanPlane → X := π ∘ planeSphere
  have hq : ContinuousOn q Ω := (hπ.comp continuous_planeSphere).continuousOn
  have havoid (x : EuclideanPlane) (hx : x ∈ Ω) : q x ∉ d.dust := by
    have hp : planeSphere x ∈ d.physicalDomain := hx
    have hu : q x ∈ d.quotientDomain := by
      change π (planeSphere x) ∈ d.quotientDomain
      rw [← he ⟨planeSphere x, hp⟩]
      exact (d.domainEquiv ⟨planeSphere x, hp⟩).property
    exact fun hb => Set.disjoint_left.mp hdisj hu hb
  obtain ⟨ι, hι, ρ, center, a, b, c, e, hlt, hrect, hsub, hpair, hdiam⟩ :=
    exists_small_shrinking_partition_refining_neighborhoods Ω q hq d.dust hB hne havoid N hN hxN
  refine ⟨ι, hι, ρ, center, a, b, c, e, hlt, ?_, hsub, hpair, ?_, ?_⟩
  · intro j
    exact physical_closed_rectangle_of_coordinate_subset ((hrect j).trans inter_subset_left)
  · intro j
    exact complex_rectangle_diameter_of_coordinate_diameter (hdiam j)

  · intro j
    exact (hrect j).trans inter_subset_right

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PartitionPlateaus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact constant values under the constructed positive smoothing. -/

open Set
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem interval_smoothing_eq_on_plateau
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (f w : EuclideanPlane → ℝ) (A V : Set EuclideanPlane) (c : ℝ)
    (hA : A ⊆ Ω) (hf : ∀x ∈ V, f x = c)
    (hpatch : ∀x ∈ A, ∀j, ρ.weight j x ≠ 0 → W j ⊆ V)
    (hinterval : ∀x ∈ Ω, ∀r s : ℝ,
      (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, f y ∈ Icc r s) → w x ∈ Icc r s) :
    ∀x ∈ A, w x = c := by
  intro x hx
  have hh := hinterval x (hA hx) c c (by
    intro j hj y hy
    rw [hf y (hpatch x hx j hj hy)]
    exact ⟨le_rfl, le_rfl⟩)
  exact le_antisymm hh.2 hh.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RelativePlateauNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Plateau refinement for relatively closed sets in the physical domain,
including terminal collars that reach deleted boundary components. -/

open Set
noncomputable section
namespace CircleDomainRigidity

theorem isOpen_relativePlateauNeighborhood {D A V : Set EuclideanPlane}
    (hA : IsOpen (D \ A)) (hV : IsOpen V) (x : EuclideanPlane) :
    IsOpen (relativePlateauNeighborhood D A V x) := by
  by_cases hx : x ∈ A
  · simpa only [relativePlateauNeighborhood, ite_eq_left hx] using hV
  · simpa only [relativePlateauNeighborhood, ite_eq_right hx] using hA

theorem self_mem_relativePlateauNeighborhood {D A V : Set EuclideanPlane}
    (hAV : A ⊆ V) {x : EuclideanPlane} (hxD : x ∈ D) :
    x ∈ relativePlateauNeighborhood D A V x := by
  by_cases hx : x ∈ A
  · simpa only [relativePlateauNeighborhood, ite_eq_left hx] using hAV hx
  · simpa only [relativePlateauNeighborhood, ite_eq_right hx] using (show x ∈ D \ A from ⟨hxD, hx⟩)

theorem relativePlateauNeighborhood_subset_of_meets
    {D A V : Set EuclideanPlane} {x y : EuclideanPlane}
    (hy : y ∈ relativePlateauNeighborhood D A V x) (hyA : y ∈ A) :
    relativePlateauNeighborhood D A V x ⊆ V := by
  by_cases hx : x ∈ A
  · simp only [relativePlateauNeighborhood, ite_eq_left hx, subset_refl]
  · have hn : y ∈ D \ A := by
      simpa only [relativePlateauNeighborhood, ite_eq_right hx] using hy
    exact (hn.2 hyA).elim

theorem partition_samples_within_relative_plateau
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    (center : ι → EuclideanPlane) (A V : Set EuclideanPlane)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆ W j)
    (hW : ∀j, W j ⊆ relativePlateauNeighborhood Ω A V (center j)) :
    ∀x ∈ A, ∀j, ρ.weight j x ≠ 0 → W j ⊆ V := by
  intro x hx j hj
  have hxW := hsub j (subset_tsupport (ρ.weight j) hj)
  exact (hW j).trans (relativePlateauNeighborhood_subset_of_meets (hW j hxW) hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalizedPhysicalPlateaus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact plateaus and bands with both global and localized gradient estimates. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_12 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_physical_smoothing_with_localized_plateaus
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A₀ V₀ A₁ V₁ : Set EuclideanPlane)
    (hA₀ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₀)) (hV₀ : IsOpen V₀) (hA₀V₀ : A₀ ⊆ V₀)
    (hA₁ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₁)) (hV₁ : IsOpen V₁) (hA₁V₁ : A₁ ⊆ V₁)
    (hA₀Ω : A₀ ⊆ physicalPlaneDomain d.physicalDomain)
    (hA₁Ω : A₁ ⊆ physicalPlaneDomain d.physicalDomain)
    (hzero : ∀x ∈ V₀, u (π (planeSphere x)) = 0)
    (hone : ∀x ∈ V₁, u (π (planeSphere x)) = 1)
    (S : Set EuclideanPlane) (hS : S ⊆ physicalPlaneDomain d.physicalDomain)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let Ω := physicalPlaneOpens d.physicalDomain hG
    ∃w : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ (∀x ∈ Ω, w x ∈ Icc 0 1) ∧
      (∀x ∈ A₀, w x = 0) ∧ (∀x ∈ A₁, w x = 1) ∧
      (∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S)) ∧
      ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤
          liminf (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ∧
        limsup (quotientPlaneRepresentative d w) (𝓝[d.quotientDomain] s) ≤
          limsup u (𝓝[d.quotientDomain] s) := by
  let Ω := physicalPlaneOpens d.physicalDomain hG
  let P : Ω → Set EuclideanPlane := fun x =>
    relativePlateauNeighborhood Ω A₀ V₀ x ∩ relativePlateauNeighborhood Ω A₁ V₁ x
  have hP (x : Ω) : IsOpen (P x) :=
    (isOpen_relativePlateauNeighborhood hA₀ hV₀ x).inter (isOpen_relativePlateauNeighborhood hA₁ hV₁ x)
  have hxP (x : Ω) : x.val ∈ P x :=
    ⟨self_mem_relativePlateauNeighborhood hA₀V₀ x.property, self_mem_relativePlateauNeighborhood hA₁V₁ x.property⟩
  obtain ⟨ι, hι, ρ, center, a, b, c, e, hlt, hphys, hsub, hpair, hdiam, hrefine⟩ :=
    exists_refined_physical_sampling_partition d hG hdisj π hπ he hB hne P hP hxP
  let : Countable ι := hι
  have hv : ∀y (hy : y ∈ d.physicalDomain),
      (u ∘ π) y = u (d.domainEquiv ⟨y, hy⟩).val := by
    intro y hy
    rw [he]
    rfl
  obtain ⟨w, hw, hunit, hinter, henergyw⟩ :=
    potential_positive_partition_smoothing_with_local_energy d hdisj ν N u hu g hg henergy
      m hm hpath (u ∘ π) hv ρ a b c e (fun j => (hlt j).1) (fun j => (hlt j).2)
      hphys hsub hdiam C hC hderiv S hS hε
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (e j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hsample₀ : ∀j, W j ⊆ relativePlateauNeighborhood Ω A₀ V₀ (center j) :=
    fun j => ((hclosed j).trans (hrefine j)).trans inter_subset_left
  have hsample₁ : ∀j, W j ⊆ relativePlateauNeighborhood Ω A₁ V₁ (center j) :=
    fun j => ((hclosed j).trans (hrefine j)).trans inter_subset_right
  refine ⟨w, hw, hunit, ?_, ?_, henergyw, ?_⟩
  · exact interval_smoothing_eq_on_plateau ρ W (fun x => u (π (planeSphere x))) w A₀ V₀ 0
      hA₀Ω hzero (partition_samples_within_relative_plateau ρ W (fun j => center j) A₀ V₀ hsub hsample₀) hinter
  · exact interval_smoothing_eq_on_plateau ρ W (fun x => u (π (planeSphere x))) w A₁ V₁ 1
      hA₁Ω hone (partition_samples_within_relative_plateau ρ W (fun j => center j) A₁ V₁ hsub hsample₁) hinter
  · exact physical_partition_band_inclusion d hG π he hinf hinfB ρ a b c e
      hphys hsub hpair u hu w hinter

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalizedContinuousCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous quotient coordinate retaining the localized physical gradient estimate. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

local instance localInst_r943510_13 : BorelSpace Sphere := ⟨rfl⟩
theorem potential_continuous_physical_coordinate_localized
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (A₀ V₀ A₁ V₁ : Set EuclideanPlane)
    (hA₀ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₀)) (hV₀ : IsOpen V₀) (hA₀V₀ : A₀ ⊆ V₀)
    (hA₁ : IsOpen (physicalPlaneDomain d.physicalDomain \ A₁)) (hV₁ : IsOpen V₁) (hA₁V₁ : A₁ ⊆ V₁)
    (hA₀Ω : A₀ ⊆ physicalPlaneDomain d.physicalDomain)
    (hA₁Ω : A₁ ⊆ physicalPlaneDomain d.physicalDomain)
    (hzero : ∀x ∈ V₀, u (π (planeSphere x)) = 0)
    (hone : ∀x ∈ V₁, u (π (planeSphere x)) = 1)
    (K : Set EuclideanPlane) (hK : IsCompact K) (hKA₀ : Kᶜ ⊆ A₀)
    (S : Set EuclideanPlane) (hS : S ⊆ physicalPlaneDomain d.physicalDomain)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : EuclideanPlane → ℝ) (Q : PhysicalRealCoordinate d π),
      ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain) ∧
      Q.quotient = quotientPlaneRepresentative d w ∧
      (∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain))) ∧
      (∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S)) ∧
      (∀x ∈ A₀, Q.quotient (π (planeSphere x)) = 0) ∧
      (∀x ∈ A₁, Q.quotient (π (planeSphere x)) = 1) ∧
      ∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤ liminf Q.quotient (𝓝[d.quotientDomain] s) ∧
        limsup Q.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s) := by
  obtain ⟨w, hw, hunit, hwzero, hwone, henergyw, hband⟩ :=
    potential_physical_smoothing_with_localized_plateaus d hdisj ν N u hu g hg henergy m hm hpath
      hG π hπ he hinf hinfB hB hne C hC hderiv A₀ V₀ A₁ V₁ hA₀ hV₀ hA₀V₀ hA₁ hV₁ hA₁V₁
      hA₀Ω hA₁Ω hzero hone S hS hε
  obtain ⟨Q, hQ, hnorm⟩ := physicalRealCoordinate_of_plane_smoothing d hG π he w hw hunit
    (fun i => (henergyw i).1) hK (fun x hx => hwzero x (hKA₀ hx))
  refine ⟨w, Q, hw, hQ, hnorm, henergyw, ?_, ?_, ?_⟩
  · intro x hx
    rw [hQ, quotientPlaneRepresentative_plane d w π he (hA₀Ω hx)]
    exact hwzero x hx
  · intro x hx
    rw [hQ, quotientPlaneRepresentative_plane d w π he (hA₁Ω hx)]
    exact hwone x hx
  · simpa only [hQ] using hband

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothedBarrierPlateaus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_one _root_.OAI.CircleDomainRigidity.complexPlaneCoordinates_zero _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.finiteCoord_coe _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the smoothing construction to the actual anchor and terminal
constant regions, choosing the averaging neighborhoods and compact exterior. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r943510_14 : BorelSpace Sphere := ⟨rfl⟩
theorem smooth_barrier_with_anchor_and_terminal
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hinf : OnePoint.infty ∈ d.physicalDomain) (hinfB : π OnePoint.infty ∉ d.dust)
    (hB : IsClosed d.dust) (hne : d.dust.Nonempty)
    (E EStar H V : Set X) (hEU : E ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior E)
    (hinfE : π OnePoint.infty ∈ interior E)
    (hH : IsClosed H) (hHV : H ⊆ V)
    (hV : IsOpen V) (hHinf : π OnePoint.infty ∉ H)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (huE : ∀x ∈ E, u x = 0) (huV : ∀x ∈ V, u x = 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (m : X → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (S : Set EuclideanPlane) (hS : S ⊆ physicalPlaneDomain d.physicalDomain)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (w : EuclideanPlane → ℝ) (Q : PhysicalRealCoordinate d π),
      ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain) ∧
      Q.quotient = quotientPlaneRepresentative d w ∧
      (∀x ∈ EStar, Q.quotient x = 0) ∧ (∀x ∈ H ∩ d.quotientDomain, Q.quotient x = 1) ∧
      (∀s ∈ d.dust, s ∈ closure d.quotientDomain →
        liminf u (𝓝[d.quotientDomain] s) ≤ liminf Q.quotient (𝓝[d.quotientDomain] s) ∧
        limsup Q.quotient (𝓝[d.quotientDomain] s) ≤ limsup u (𝓝[d.quotientDomain] s)) ∧
      ∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict S) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)))
              2 (volume.restrict S) := by
  let F := EStar ∪ {π OnePoint.infty}
  have hF : IsCompact F := hEStar.union isCompact_singleton
  have hFE : F ⊆ interior E := union_subset hEStarE (singleton_subset_iff.mpr hinfE)
  obtain ⟨A, U, hA, hU, hFA, hAU, hUE⟩ := exists_closed_anchor_plateau hF hFE
  let Ω := physicalPlaneDomain d.physicalDomain
  let q := π ∘ planeSphere
  let A₀ := Ω ∩ q ⁻¹' A
  let V₀ := Ω ∩ q ⁻¹' U
  let A₁ := Ω ∩ q ⁻¹' H
  let V₁ := Ω ∩ q ⁻¹' V
  have hΩ : IsOpen Ω := isOpen_physicalPlaneDomain hG
  have hq : Continuous q := hπ.comp continuous_planeSphere
  have hV₀ : IsOpen V₀ := hΩ.inter (hU.preimage hq)
  have hV₁ : IsOpen V₁ := hΩ.inter (hV.preimage hq)
  have hA₀V₀ : A₀ ⊆ V₀ := fun _ hx => ⟨hx.1, hAU hx.2⟩
  have hA₁V₁ : A₁ ⊆ V₁ := fun _ hx => ⟨hx.1, hHV hx.2⟩
  have hzero : ∀x ∈ V₀, u (π (planeSphere x)) = 0 := fun _ hx => huE _ (hUE hx.2)
  have hone : ∀x ∈ V₁, u (π (planeSphere x)) = 1 := fun _ hx => huV _ hx.2
  have hAVinf : π OnePoint.infty ∈ interior A := hFA (Or.inr rfl)
  have hnhds : d.physicalDomain ∩ π ⁻¹' interior A ∈ 𝓝 OnePoint.infty :=
    (hG.inter (isOpen_interior.preimage hπ)).mem_nhds ⟨hinf, hAVinf⟩
  obtain ⟨K, hK, houtside⟩ := exists_compact_plane_exterior_of_nhds hnhds
  have hKA₀ : Kᶜ ⊆ A₀ := by
    intro x hx
    refine ⟨(houtside x hx).1, ?_⟩
    change π (planeSphere x) ∈ A
    exact interior_subset (show π (planeSphere x) ∈ interior A from (houtside x hx).2)
  obtain ⟨w, Q, hw, hQ, _, hnorm, hQ₀, hQ₁, hband⟩ :=
    potential_continuous_physical_coordinate_localized d hdisj ν N u hu g hg henergy m hm hpath
      hG π hπ he hinf hinfB hB hne C hC hderiv A₀ V₀ A₁ V₁
      (physical_plateau_relative_complement_open hG hπ hA) hV₀ hA₀V₀
      (physical_plateau_relative_complement_open hG hπ hH) hV₁ hA₁V₁
      inter_subset_left inter_subset_left hzero hone K hK hKA₀ S hS hε
  refine ⟨w, Q, hw, hQ, ?_, ?_, hband, fun i => ⟨(hnorm i).1, (hnorm i).2.2⟩⟩
  · intro x hx
    by_cases hxi : x = π OnePoint.infty
    · rw [hxi, hQ, ← he ⟨OnePoint.infty, hinf⟩,
        quotientPlaneRepresentative_on_domain d w OnePoint.infty hinf]
      simp [sphereFromPlaneFunction]
    · have hxU : x ∈ d.quotientDomain := hEU (interior_subset (hEStarE hx))
      obtain ⟨z, hz, hzq⟩ := quotient_finite_plane_covers d π he ⟨hxU, by simpa using hxi⟩
      change π (planeSphere z) = x at hzq
      rw [← hzq]
      apply hQ₀ z
      refine ⟨hz, ?_⟩
      change π (planeSphere z) ∈ A
      rw [hzq]
      exact interior_subset (hFA (Or.inl hx))
  · intro x hx
    have hxU := hx.2
    have hxi : x ≠ π OnePoint.infty := fun heq => hHinf (heq ▸ hx.1)
    obtain ⟨z, hz, hzq⟩ := quotient_finite_plane_covers d π he ⟨hxU, by simpa using hxi⟩
    change π (planeSphere z) = x at hzq
    rw [← hzq]
    apply hQ₁ z
    refine ⟨hz, ?_⟩
    change π (planeSphere z) ∈ H
    simpa only [hzq] using hx.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FilledSmoothBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compatible smooth barrier from the first-arrival obstruction.
The norm outside the penalty region depends only on the original density;
the perturbation is used solely to obtain the plateaus and path inequality. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_r943510_15 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_compatible_smooth_first_arrival_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (E EStar : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior E)
    (hinfE : π OnePoint.infty ∈ interior E)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hN : ∀n labels, (Measure.pi (fun _ : Fin (n + 1) =>
      (volume : Measure UnitAddCircle))) (N n labels) = 0)
    (F : Set Sphere) (hF : MeasurableSet F) (hFB : F ⊆ d.dust)
    (hmF : ∀x ∈ F, m x = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃(k l : ℕ) (O : Set Sphere) (Q : PhysicalRealCoordinate d π),
      k < l ∧ IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      (∀x ∈ EStar, Q.quotient x = 0) ∧
      (∀x ∈ closure (D l).region ∩ d.quotientDomain, Q.quotient x = 1) ∧
      (∀s ∈ d.dust, ENNReal.ofReal (limsup Q.quotient (𝓝[d.quotientDomain] s) -
        liminf Q.quotient (𝓝[d.quotientDomain] s)) ≤ 4 * m s) ∧
      (∀i : Fin 2, eLpNorm (fun y => (fderiv ℝ Q.physical y)
          (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain \
            (fun y : ℝ × ℝ => π (Complex.equivRealProdCLM.symm y : Sphere)) ⁻¹' O)) ≤
        ε + ENNReal.ofReal (4 * (9 * C)) *
          (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)) ∧
      ∀n labels, (volume.prod (Measure.pi (fun _ : Fin (n + 1) =>
        (volume : Measure UnitAddCircle))))
        (freeComponentFailure F (circleBandGraph d.quotientDomain Q.quotient)
          (fun i => circleBandGraph d.quotientDomain (previous i).quotient) labels) = 0 := by
  obtain ⟨k, O, g₁, u, hO, hOU, hEO, hfO, hg₁, _, hagree, henergy₁,
    hu, huE, huD, hpath, hband⟩ := exists_filled_first_arrival_barrier_potential
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hdisj hBU
      hdense hinfty hbad ν N E hE hEU p hpDust hp D hnest hshrink hED f hf W₁ W₂
      hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
  have hDk := (D k).isOpen_region hπ hclosed hsurj hr
  obtain ⟨j, hj⟩ := hshrink ((D k).region \ {π OnePoint.infty})
    ((hDk.sdiff isClosed_singleton).mem_nhds ⟨(D k).point_mem_region hsurj hp, hp⟩)
  let l := max j (k + 1)
  have hl : closure (D l).region ⊆ (D k).region \ {π OnePoint.infty} :=
    hj l (le_max_left _ _)
  let T : Set (ℝ × ℝ) := FiniteTransfer.realChartDomain d.physicalDomain \
    (fun y : ℝ × ℝ => π (Complex.equivRealProdCLM.symm y : Sphere)) ⁻¹' O
  let S := euclideanPlaneCoordinates ⁻¹' T
  have hT : MeasurableSet T :=
    (FiniteTransfer.isOpen_realChartDomain hG).measurableSet.diff
      ((hO.preimage (hπ.comp (OnePoint.continuous_coe.comp
        Complex.equivRealProdCLM.symm.continuous))).measurableSet)
  have hS : S ⊆ physicalPlaneDomain d.physicalDomain := fun _ hx => hx.1
  obtain ⟨v, Q, hv, hQ, hzero, hone, hcontract, hnorm⟩ :=
    smooth_barrier_with_anchor_and_terminal d hG hdisj π hπ he hinf hinfty hB ⟨p, hpDust⟩
      E EStar (closure (D l).region) (D k).region hEU hEStar hEStarE hinfE
      isClosed_closure (fun x hx => (hl hx).1) hDk
      (fun hx => (hl hx).2 rfl) ν N u hu huE (fun x hx => huD x (subset_closure hx))
      g₁ hg₁ henergy₁ m hm hpath C hC hderiv S hS hε
  refine ⟨k, l, O, Q, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _),
    hO, hOU, hEO, hfO, hzero, hone, ?_, ?_, ?_⟩
  · intro s hs
    apply le_trans (ENNReal.ofReal_le_ofReal (sub_le_sub (hcontract s hs
      (by rw [hdense.closure_eq]; trivial)).2 (hcontract s hs
      (by rw [hdense.closure_eq]; trivial)).1)) (hband s hs)
  · intro i
    have hlocal := (hnorm i).1.mono_measure (Measure.restrict_mono_set volume hS)
    rw [physical_coordinate_partial_eLpNorm_on d hG π he v hv Q hQ hT
      (fun _ hx => hx.1) i hlocal]
    refine (hnorm i).2.trans (add_le_add le_rfl ?_)
    exact localized_perturbed_density_eLpNorm_le π O S
      (hT.preimage euclideanPlaneCoordinates.continuous.measurable) (fun _ hx => hx.2)
      g g₁ hg henergy hagree (4 * (9 * C)) (by positivity)
  · intro n labels
    apply smoothed_barrier_compatibility_with_physical_coordinates hcoarea hLusin d hU hG hdisj
      π hπ hsurj hfiber (fun y => (he y).symm) hB.isCompact hTD
      (by rintro _ ⟨y, hy, rfl⟩; exact hbad y hy) hBU hdisj
      (by rw [hdense.closure_eq]; exact subset_univ _) hF hFB harcs previous hlevels
      g₁ hg₁ henergy₁ m hm₂ hmF hweights hpoint ν N u hu hpath hband Q
      (fun s hs => hcontract s hs (by rw [hdense.closure_eq]; trivial)) n labels (hN n labels)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierConstruction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compatible barrier theorem with the enlarged flags and the full
controlled size, constructed from the actual first-arrival cost bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_r943510_16 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_controlled_compatible_real_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ d.anchor → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hN : ∀n labels, (Measure.pi (fun _ : Fin (n + 1) =>
      (volume : Measure UnitAddCircle))) (N n labels) = 0)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃ R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      R.controlledSize ≤ 2 * (ε + ENNReal.ofReal (4 * (9 * C)) *
        squareIntegralNorm sphericalArea g) + 4 * countingSquareNorm m := by
  let exceptions := flags ∪ support m
  have hcount : exceptions.Countable := hflags.union (countable_square_toll_support hm₂)
  let F := d.dust \ exceptions
  have hF : MeasurableSet F := hB.measurableSet.diff hcount.measurableSet
  have hmF : ∀x ∈ F, m x = 0 := by
    intro x hx
    by_contra hz
    exact hx.2 (Or.inr hz)
  obtain ⟨_, l, O, Q, _, hO, hOU, hEO, hfO, hzero, hone, hband, hnorm, hcompat⟩ :=
    exists_compatible_smooth_first_arrival_barrier hcoarea hLusin hsard hsch
      d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν N hinf
      d.anchor EStar hE hEU hEStar hEStarE hinfE p hpDust hp D hnest hshrink hED
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
      hfiber harcs previous hlevels hweights hN F hF inter_subset_left hmF C hC hderiv hε
  have hweight : (∑'s, (4 * m s) ^ 2) < ∞ := by
    simp_rw [mul_pow]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by norm_num) hm₂.lt_top
  let R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁ := {
    coordinate := Q
    level := l
    penalty := O
    penalty_open := hO
    penalty_inside := hOU
    penalty_disjoint := hEO
    penalty_avoids := hfO
    zero := hzero
    one := hone
    exclusions := exceptions
    exclusions_countable := hcount
    prior_flags := subset_union_left
    weight := fun s => 4 * m s
    weight_finite := hweight
    weight_support := fun s hs => Or.inr (fun hz => hs (by
      change 4 * m s = 0
      rw [hz, mul_zero]))
    band_bound := hband
    compatible := hcompat }
  refine ⟨R, ?_⟩
  have hA : ε + ENNReal.ofReal (4 * (9 * C)) * squareIntegralNorm sphericalArea g ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨hεfin, ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) ?_⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) henergy.ne
  have hR := R.controlledSize_le_of_partial_bounds hA hnorm
  simpa only [R, countingSquareNorm_mul] using hR

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModulusNormBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing a pointwise lower bound for every admissible metric to the
measure-family modulus. The metrics retain extended values. -/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {A Z : Type*} [MeasurableSpace Z]

theorem le_modulus_of_admissible_norm_bound
    (σ : Measure Z) (K : A → FiniteMeasure Z) (c : ℝ≥0∞)
    (hbound : ∀h : Z → ℝ≥0∞, Measurable h →
      (∀a, 1 ≤ ∫⁻z, h z ∂(K a : Measure Z)) → c ≤ squareIntegralNorm σ h) :
    c ^ 2 ≤ measureFamilyModulus A Z σ K := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro hadm
  have hb := pow_le_pow_left' (hbound h hh hadm) 2
  have he : (squareIntegralNorm σ h) ^ 2 = ∫⁻z, h z ^ 2 ∂σ := by
    rw [squareIntegralNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  exact hb.trans_eq he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExtendedAtomicToll
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a prescribed countable atomic metric by zero on the quotient.
Both its square norm and the full preterminal visit payment are preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem extendAtomicToll_apply {D X : Type*} {p : D → X}
    (hp : Injective p) (m : D → ℝ≥0∞) (s : D) :
    extendAtomicToll p m (p s) = m s := hp.extend_apply m 0 s

theorem extendAtomicToll_zero {D X : Type*} (p : D → X) (m : D → ℝ≥0∞)
    {x : X} (hx : x ∉ range p) : extendAtomicToll p m x = 0 :=
  Function.extend_apply' (f := p) m (fun _ : X => 0) x hx

theorem countingSquareNorm_extendAtomicToll {D X : Type*} {p : D → X}
    (hp : Injective p) (m : D → ℝ≥0∞) :
    countingSquareNorm (extendAtomicToll p m) = countingSquareNorm m := by
  unfold countingSquareNorm
  congr 1
  calc
    (∑'x, extendAtomicToll p m x ^ 2) = ∑'s, extendAtomicToll p m (p s) ^ 2 := by
      symm
      apply hp.tsum_eq (f := fun x : X => extendAtomicToll p m x ^ 2)
      intro x hx
      by_contra h
      exact hx (by
        change extendAtomicToll p m x ^ 2 = 0
        rw [extendAtomicToll_zero p m h, zero_pow (by decide)])
    _ = _ := by simp only [extendAtomicToll_apply hp]

theorem preterminalToll_extendAtomicToll {D X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {p : D → X} (hp : Injective p) (m : D → ℝ≥0∞) :
    preterminalToll γ (extendAtomicToll p m) =
      ∑'s, m s * preterminalVisitCount γ (p s) := by
  rw [preterminalToll_eq_visits]
  calc
    (∑'x, extendAtomicToll p m x * preterminalVisitCount γ x) =
        ∑'s, extendAtomicToll p m (p s) * preterminalVisitCount γ (p s) := by
      symm
      apply hp.tsum_eq (f := fun x : X => extendAtomicToll p m x * preterminalVisitCount γ x)
      intro x hx
      by_contra h
      exact hx (by
        change extendAtomicToll p m x * preterminalVisitCount γ x = 0
        rw [extendAtomicToll_zero p m h, zero_mul])
    _ = _ := by simp only [extendAtomicToll_apply hp]


theorem perturbed_endpoint_cost_ge_one
    {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace D] [BorelSpace D] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (p : D → X) (hp : Injective p) (c : D → ℝ≥0∞)
    (ν : Measure X) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hadm : CostAdmissible d p c ν h) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) (ρ.val, θ)) :
    1 ≤ (∫⁻y, perturbedPhysicalDensity h δ y
      ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (extendAtomicToll p (perturbedAtomicToll h c δ)) := by
  let Γ := forgetCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) ⟨(ρ.val, θ), hΓ⟩
  have hcost := perturbed_cost_ge_one d p c ν Γ h hh hΓ hadm hδ
  rw [preterminalToll_extendAtomicToll _ hp]
  exact hcost

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PerturbedBarrierData
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An admissible extended coding metric supplies the actual positive
physical density, countable quotient tolls, and endpoint cost used by the
barrier theorem. No restriction on values on area-null sets is imposed. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r943510_17 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_perturbed_barrier_data
    {D : Type*} [TopologicalSpace D] [Countable D]
    [MeasurableSpace D] [BorelSpace D]
    [MeasurableSpace C(PathTime, Sphere)]
    (d : PathCodeData Sphere Sphere) (p : D → Sphere) (hp : Injective p)
    (c : D → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ν : Measure Sphere) (τ : Measure LevelTuple)
    (h : PathCostSpace Sphere D → ℝ≥0∞) (hh : Measurable h)
    (hadm : CostAdmissible d p c ν h)
    (he : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c τ) < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃(δ : ℝ≥0) (g : Sphere → ℝ≥0∞) (m : Sphere → ℝ≥0∞),
      0 < δ ∧ Measurable g ∧ (∀y, (δ : ℝ≥0∞) ≤ g y) ∧
      (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞ ∧ (∑'x, m x ^ 2) < ∞ ∧
      (∀x ∉ range p, m x = 0) ∧
      squareIntegralNorm sphericalArea g + countingSquareNorm m ≤
        2 * squareIntegralNorm (pathCostReference sphericalArea c τ) h + ε ∧
      ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) (ρ.val, θ) →
        1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
          preterminalToll ρ.val m := by
  obtain ⟨δ, hδ, hsize⟩ := exists_small_positive_perturbation sphericalArea c hc τ hh hε
  let g := perturbedPhysicalDensity h (δ : ℝ≥0∞)
  let a := perturbedAtomicToll h c (δ : ℝ≥0∞)
  let m := extendAtomicToll p a
  have hext : countingSquareNorm m = countingSquareNorm a := countingSquareNorm_extendAtomicToll hp a
  have hsize' : squareIntegralNorm sphericalArea g + countingSquareNorm m ≤
      2 * squareIntegralNorm (pathCostReference sphericalArea c τ) h + ε := by
    simpa only [hext] using hsize
  have hnorm : squareIntegralNorm sphericalArea g + countingSquareNorm m < ∞ :=
    lt_of_le_of_lt hsize' (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) he.ne)),
        lt_top_iff_ne_top.mpr hεfin⟩)
  have hgfinite : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞ := by
    have hn := lt_of_le_of_lt le_self_add hnorm
    by_contra ht
    have ht' : (∫⁻y, g y ^ 2 ∂sphericalArea) = ∞ := top_unique (not_lt.mp ht)
    simp [squareIntegralNorm, ht'] at hn
  have hmfinite : (∑'x, m x ^ 2) < ∞ := by
    have hn := lt_of_le_of_lt le_add_self hnorm
    by_contra ht
    have ht' : (∑'x, m x ^ 2) = ∞ := top_unique (not_lt.mp ht)
    simp [countingSquareNorm, ht'] at hn
  exact ⟨δ, g, m, hδ, (hh.comp measurable_costPhysical).add_const _,
    (fun _ => le_add_self), hgfinite, hmfinite,
    (fun _ hx => extendAtomicToll_zero p a hx), hsize',
    fun ρ θ hΓ => perturbed_endpoint_cost_ge_one d p hp c ν h hh hadm
      (ENNReal.coe_pos.mpr hδ) ρ θ hΓ⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierTrialMetric
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Failure of a small actual compatible barrier gives a uniform lower
bound on every admissible coding metric. The excluded tuples and positive
perturbations are constructed from that metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem barrierConstructionConstant_ne_top (C : ℝ) : barrierConstructionConstant C ≠ ∞ := by
  apply ne_of_lt
  exact max_lt_iff.mpr ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top, by norm_num⟩

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_r943510_18 : BorelSpace Sphere := ⟨rfl⟩
theorem trial_metric_norm_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    (h : PathCostSpace Sphere A → ℝ≥0∞) (hh : Measurable h)
    (heh : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c (tupleReference ω)) < ∞)
    (hadm : CostAdmissible d a c ν h)
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize) :
    β ≤ 2 * barrierConstructionConstant C *
      squareIntegralNorm (pathCostReference sphericalArea c (tupleReference ω)) h := by
  let K := barrierConstructionConstant C
  have hK : K ≠ ∞ := barrierConstructionConstant_ne_top C
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hpos : 0 < (ε : ℝ≥0∞) := ENNReal.coe_pos.mpr hε
  have hKadd : 2 + K ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hK⟩
  obtain ⟨η, hη, hηsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hKadd hpos.ne'
  obtain ⟨δ, g, m, hδ, hg, hpositive, hge, hme, hmoff, hsize, hcost⟩ :=
    exists_perturbed_barrier_data d a ha c hc ν (tupleReference ω) h hh hadm heh
      (ENNReal.coe_pos.mpr hη) ENNReal.coe_ne_top
  let N := tupleInfiniteExclusions (h ∘ costTuple)
  have hN (n : ℕ) (labels : Fin (n + 1) → ℕ) :
      (Measure.pi (fun _ : Fin (n + 1) => (volume : Measure UnitAddCircle))) (N n labels) = 0 :=
    null_tupleExclusions_of_reference_energy sphericalArea c ω hω h hh heh n labels
  have hm : ∀x ∈ d.quotientDomain, m x = 0 := by
    intro x hx
    apply hmoff
    intro hxa
    exact Set.disjoint_left.mp hdisj hx (haB hxa)
  have hunit (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
      (hallowed : AllowedTaggedPath d ν N (ρ.val, θ)) (hstart : ρ.val ⊥ ∈ d.anchor)
      (hend : ρ.val ⊤ = p) (hfirst : ∀t < (⊤ : PathTime), ρ.val t ≠ p)
      (hgate : GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val) :
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m := by
    apply hcost ρ θ
    refine ⟨hallowed, ⟨hstart, ?_⟩, ?_⟩
    · rw [htarget]
      exact ⟨hend, hfirst⟩
    · simpa only [hcontours, hgates] using hgate
  obtain ⟨R, hR⟩ := exists_controlled_compatible_real_barrier
    hcoarea hLusin hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he
    hB hTD hBU hdense hinfty hbad ν N hinf EStar hE hEU hEStar hEStarE hinfE
    p hpDust hp D hnest hshrink hED f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg hge m hm hme.ne
    (δ : ℝ≥0∞) (ENNReal.coe_pos.mpr hδ).ne' (fun y _ => hpositive y) hpoint hunit
    hfiber harcs previous hlevels hweights hN flags hflags C hC hderiv
    (ENNReal.coe_pos.mpr hη) ENNReal.coe_ne_top
  refine (hno R).trans (hR.trans ?_)
  calc
    2 * (↑η + ENNReal.ofReal (4 * (9 * C)) * squareIntegralNorm sphericalArea g) +
        4 * countingSquareNorm m =
      2 * ↑η + (2 * ENNReal.ofReal (4 * (9 * C))) * squareIntegralNorm sphericalArea g +
        4 * countingSquareNorm m := by ring
    _ ≤ 2 * ↑η + K * squareIntegralNorm sphericalArea g + K * countingSquareNorm m := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul' (le_max_left _ _) le_rfl))
        (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = 2 * ↑η + K * (squareIntegralNorm sphericalArea g + countingSquareNorm m) := by ring
    _ ≤ 2 * ↑η + K * (2 * squareIntegralNorm
        (pathCostReference sphericalArea c (tupleReference ω)) h + ↑η) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hsize)
    _ = 2 * K * squareIntegralNorm (pathCostReference sphericalArea c (tupleReference ω)) h +
        ↑η * (2 + K) := by ring
    _ ≤ _ := add_le_add le_rfl hηsmall.le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CodeModulusExtraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measure-family duality and probability lifting produce a law on the
constrained codes from a positive modulus bound. -/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [BorelSpace D] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] in
theorem costAdmissible_iff_constrained (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (h : PathCostSpace Y D → ℝ≥0∞) :
    CostAdmissible d p c ν h ↔
      ∀ Γ : ConstrainedCostCode d p c ν,
        1 ≤ ∫⁻ z, h z ∂(constrainedCodeMeasure d p c ν Γ : Measure (PathCostSpace Y D)) := by
  constructor
  · intro hadm Γ
    exact hadm Γ.val.val Γ.val.property Γ.property
  · intro hadm Γ hfinite hres
    exact hadm ⟨⟨Γ, hfinite⟩, hres⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform modulus bound, derived from the constructed compatible
barrier and valid for the actual finite constrained coding-measure family. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_r943510_19 : BorelSpace Sphere := ⟨rfl⟩
theorem barrier_modulus_lower_bound_oai
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (hB : IsClosed d.dust) (hTD : IsTotallyDisconnected d.dust)
    (hBU : d.dustᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ d.dust)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ d.dust)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (hinf : OnePoint.infty ∈ d.physicalDomain)
    (EStar : Set Sphere) (hE : IsClosed d.anchor) (hEU : d.anchor ⊆ d.quotientDomain)
    (hEStar : IsCompact EStar) (hEStarE : EStar ⊆ interior d.anchor)
    (hinfE : π OnePoint.infty ∈ interior d.anchor)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π d.dust p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint d.anchor (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (hfiber : ∀x, IsConnected (π ⁻¹' {x}))
    (harcs : ∀C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (previous : ℕ → PhysicalRealCoordinate d π)
    (hlevels : ∀i, d.levels i = Prod.swap ⁻¹'
      circleBandGraph d.quotientDomain (previous i).quotient)
    (hweights : ∀i, (∑'x, d.levelWeights i x ^ 2) ≠ ∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (flags : Set Sphere) (hflags : flags.Countable)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (htarget : d.target = p)
    (hcontours : d.gateContours = fun j => frontier (D j).region)
    (hgates : d.gateSets = fun _ => Subtype.val '' (f ⁻¹' closure W₂))
    {A : Type*} [TopologicalSpace A] [Countable A] [MeasurableSpace A] [BorelSpace A]
    (a : A → Sphere) (ha : Injective a) (haB : range a ⊆ d.dust)
    (c : A → ℝ≥0∞) (hc : (∑'s, c s ^ 2) < ∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀i, ω i ≠ 0)
    [PolishSpace A] [StandardBorelSpace (ConstrainedCostCode d a c ν)]
    (β : ℝ≥0∞)
    (hno : ∀R : CompatibleRealBarrier d π previous flags EStar (fun j => (D j).region) f W₁,
      β ≤ R.controlledSize) :
    (β / (2 * barrierConstructionConstant C)) ^ 2 ≤
      measureFamilyModulus (ConstrainedCostCode d a c ν) (PathCostSpace Sphere A)
        (pathCostReference sphericalArea c (tupleReference ω)) (constrainedCodeMeasure d a c ν) := by
  apply le_modulus_of_admissible_norm_bound
  intro h hh hadm
  by_cases heh : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c (tupleReference ω)) < ∞
  · apply ENNReal.div_le_of_le_mul'
    exact trial_metric_norm_lower_bound hcoarea hLusin hsard hsch d hU hG hdisj
      π hπ hclosed hsurj hr he hB hTD hBU hdense hinfty hbad ν hinf EStar hE hEU hEStar hEStarE
      hinfE p hpDust hp D hnest hshrink hED f hf W₁ W₂ hW₁ hW₂ hW₁₂ hfiber harcs previous
      hlevels hweights hpoint flags hflags C hC hderiv htarget hcontours hgates a ha haB c hc ω hω
      h hh heh ((costAdmissible_iff_constrained d a c ν h).mpr hadm) β hno
  · have ht : (∫⁻z, h z ^ 2 ∂pathCostReference sphericalArea c (tupleReference ω)) = ∞ :=
      top_unique (not_lt.mp heh)
    simp [squareIntegralNorm, ht]

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CircleDomainRigidity.barrier_modulus_lower_bound_oai.{u_1} := @OAI.CircleDomainRigidity.barrier_modulus_lower_bound_oai.{u_1}
