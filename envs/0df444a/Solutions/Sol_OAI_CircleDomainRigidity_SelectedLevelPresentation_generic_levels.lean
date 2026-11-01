-- Prove2me | solution 1 for OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:46:32.675375+00:00
-- url     : https://prove2.me/submissions/c0e9435f-6555-48fd-9978-c28a65fc6898

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

/-- Adjoining totally disconnected dust to a closed set creates no new
nondegenerate continuum. This is the first small-disk lemma of the paper. -/
theorem continuum_subset_closed_of_totallyDisconnected
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C F B : Set X} (hC : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) (hF : IsClosed F) (hB : IsTotallyDisconnected B)
    (hsub : C ⊆ F ∪ B) : C ⊆ F := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  intro x hx
  by_contra hxF
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := ((Subtype.val : C → X) ⁻¹' F)ᶜ ∩ {yc}ᶜ
  have hO : IsOpen O := (hF.preimage continuous_subtype_val).isOpen_compl.inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxF, fun h => hyx (congrArg Subtype.val h).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro h
    have hyN : yc ∈ N := by rw [h]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hzC, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  have hconnN : IsPreconnected (connectedComponentIn N xc) :=
    isPreconnected_connectedComponentIn
  have himageB : (Subtype.val : C → X) '' connectedComponentIn N xc ⊆ B := by
    rintro _ ⟨w, hw, rfl⟩
    have hwN := connectedComponentIn_subset N xc hw
    exact (hsub w.property).resolve_left (hNO hwN).1
  have hsingle := hB _ himageB (hconnN.image _ continuous_subtype_val.continuousOn)
  have hzxeq : z.val = x := hsingle ⟨z, hzC, rfl⟩
    ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzxc : z = xc := Subtype.ext hzxeq
  have hxfront : xc ∈ frontier N := hzxc ▸ hzfront
  exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Selection_BandGraph
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!+# Compact interval-band graphs for bounded real coordinates

Take the closure of the physical graph and fill the interval between
cluster values in each fiber. This constructs a compact band graph;
on the open physical domain it is exactly the original graph. Its
projection modulo one consequently gives compact level sets with the
correct physical fibers.
-/

open Set

namespace CircleDomainRigidity

theorem isCompact_circleBandLevel {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ x ∈ G, |f x| ≤ M)
    (t : AddCircle (1 : ℝ)) : IsCompact {x | (x, t) ∈ circleBandGraph G f} :=
  ((isCompact_circleBandGraph hM).isClosed.preimage (continuous_id.prodMk continuous_const)).isCompact

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactBandNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton fibers of a compact band graph have uniformly narrow
nearby fibers. This gives the local branch ranges used near free points. -/

open Set
open scoped Topology

namespace CircleDomainRigidity

theorem exists_open_compact_band_range
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) {x : X} {W : Set ℝ}
    (hW : IsOpen W) (hfiber : ∀ t, (x, t) ∈ K → t ∈ W) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ t, (y, t) ∈ K → t ∈ W := by
  let F := Prod.fst '' (K ∩ Prod.snd ⁻¹' Wᶜ)
  have hF : IsClosed F :=
    ((hK.inter_right (hW.isClosed_compl.preimage continuous_snd)).image continuous_fst).isClosed
  refine ⟨Fᶜ, hF.isOpen_compl, ?_, ?_⟩
  · rintro ⟨⟨y, t⟩, ⟨ht, hnot⟩, hy⟩
    change y = x at hy
    subst y
    exact hnot (hfiber t ht)
  · intro y hy t ht
    by_contra hnot
    exact hy ⟨(y, t), ⟨ht, hnot⟩, rfl⟩

theorem exists_narrow_real_band_neighborhood
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} {a : ℝ}
    (htrace : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ioo (a - ε) (a + ε) := by
  apply exists_open_compact_band_range
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM)) isOpen_Ioo
  intro t ht
  rw [htrace t ht]
  constructor <;> linarith

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ambient tagged-path code space and its compact residual-time sections.
An active slot contains a nonempty finite label tuple, its circle levels,
and the two ends of its open time interval. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem residualTimes_eq {X : Type*} [TopologicalSpace X] (B : Set X) (Γ : TaggedPath X) :
    residualTimes B Γ = Γ.1 ⁻¹' B \ ⋃ k, Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
  ext t
  simp only [residualTimes, residualTimeGraph, mem_ofPred_eq, mem_sdiff,
    mem_preimage, mem_iUnion, mem_Ioo, not_exists, not_and_or, not_lt]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_TaggedNullTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining all open tags with the residual constraint gives a null
free trace for the complete coded path. No incidence measurability is
assumed for this pathwise outer-measure argument. -/

open Set MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem tagged_free_trace_null
    {X : Type*} [TopologicalSpace X] (B Free : Set X) (hFree : Free ⊆ B)
    (Γ : TaggedPath X) (w : X → UnitAddCircle)
    (hresidual : volume (w '' (Γ.1 '' residualTimes B Γ ∩ Free)) = 0)
    (htags : ∀ k, volume (w ''
      (Γ.1 '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) ∩ Free)) = 0) :
    volume (w '' (range Γ.1 ∩ Free)) = 0 := by
  apply measure_mono_null (t := (w '' (Γ.1 '' residualTimes B Γ ∩ Free)) ∪
    ⋃ k, w '' (Γ.1 '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) ∩ Free))
  · rintro _ ⟨x, ⟨⟨t, rfl⟩, hx⟩, rfl⟩
    by_cases ht : ∃ k, t ∈ Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k))
    · obtain ⟨k, hk⟩ := ht
      exact Or.inr (mem_iUnion.mpr ⟨k, Γ.1 t, ⟨⟨t, hk, rfl⟩, hx⟩, rfl⟩)
    · apply Or.inl
      refine ⟨Γ.1 t, ⟨⟨t, ?_, rfl⟩, hx⟩, rfl⟩
      rw [residualTimes_eq]
      exact ⟨hFree hx, fun h => ht (mem_iUnion.mp h)⟩
  · exact measure_union_null hresidual (measure_iUnion_null htags)

theorem free_level_incidence_null_of_trace
    {X T : Type*} [TopologicalSpace X] [MeasurableSpace T]
    (ν : Measure T) (γ : C(PathTime, X)) (Free : Set X) (w : X → T)
    (H : Set (T × X)) (hlevel : ∀ x ∈ Free, ∀ t, (t, x) ∈ H → w x = t)
    (htrace : ν (w '' (range γ ∩ Free)) = 0) :
    ν {t | ∃ x ∈ range γ ∩ Free, (t, x) ∈ H} = 0 := by
  apply measure_mono_null _ htrace
  rintro t ⟨x, hx, hxt⟩
  exact ⟨x, hx, hlevel x hx.2 t hxt⟩

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


omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
theorem one_le_visitCount_of_hit {γ : C(PathTime, X)} {x : X}
    (h : ∃ t, γ t = x) : 1 ≤ visitCount γ x := by
  obtain ⟨t, ht⟩ := h
  have h1 := visitCount_ge_nat (γ := γ) (x := x) (n := 1)
    ⟨fun _ => t, fun _ _ _ => Subsingleton.elim _ _, fun _ => ht⟩
  simpa only [Nat.cast_one] using h1

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem pathHitProbability_le_meanVisitCount (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitProbability μ x ≤ meanVisitCount μ x := by
  let H : Set C(PathTime, X) := {γ | ∃ t, γ t = x}
  calc
    pathHitProbability μ x = ∫⁻ γ, H.indicator (fun _ => (1 : ℝ≥0∞)) γ
        ∂(μ : Measure C(PathTime, X)) := by
      rw [lintegral_indicator (isClosed_paths_hitting x).measurableSet]
      simp only [lintegral_one, Measure.restrict_apply_univ]
      rfl
    _ ≤ meanVisitCount μ x := by
      apply lintegral_mono
      intro γ
      by_cases h : γ ∈ H
      · simpa only [Set.indicator_of_mem h] using one_le_visitCount_of_hit h
      · simp only [Set.indicator_of_notMem h]
        exact bot_le

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
-- module Solutions.Q146_CD.CircleDomains_Topology_PathTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary tolls count every parameter visit. Counting-square-summable
weights have countable support, so their true tolls are Borel. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem boundaryToll_eq_visits (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x, m x * visitCount γ x := by
  rw [boundaryToll, ← ENNReal.tsum_fiberwise (fun t => m (γ t)) γ]
  apply tsum_congr
  intro x
  rw [visitCount_eq_tsum, ← ENNReal.tsum_mul_left,
    tsum_subtype (γ ⁻¹' {x}) (fun t : PathTime => m (γ t))]
  apply tsum_congr
  intro t
  by_cases h : γ t = x
  · simp [h, Set.indicator]
  · simp [h, Set.indicator]

theorem boundaryToll_eq_support (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = ∑' x : Function.support m, m x * visitCount γ x := by
  rw [boundaryToll_eq_visits]
  symm
  apply tsum_subtype_eq_of_support_subset (f := fun x : X => m x * visitCount γ x)
  intro x hx
  contrapose! hx
  simp only [Function.mem_support] at hx ⊢
  simp [hx]

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_boundaryToll {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    Measurable (fun γ : C(PathTime, X) => boundaryToll γ m) := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  exact Measurable.tsum fun x => measurable_const.mul
    (measurable_visitCount.comp (measurable_id.prodMk measurable_const))

theorem lintegral_boundaryToll (μ : ProbabilityMeasure C(PathTime, X))
    {m : X → ℝ≥0∞} (hm : (Function.support m).Countable) :
    ∫⁻ γ, boundaryToll γ m ∂(μ : Measure _) =
      ∑' x : Function.support m, m x * meanVisitCount μ x := by
  let : Countable (Function.support m) := hm.to_subtype
  simp_rw [boundaryToll_eq_support]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro x
    exact lintegral_const_mul _
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))
  · intro x
    exact (measurable_const.mul
      (measurable_visitCount.comp (measurable_id.prodMk measurable_const))).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualVisits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual residual visit multiplicities and tolls on closed test intervals. -/

open Set Function MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem residualToll_eq_visits (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = ∑' x, m x * residualVisitCount B I Γ x := by
  rw [residualToll, ← ENNReal.tsum_fiberwise
    (fun t => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0) Γ.1]
  apply tsum_congr
  intro x
  rw [residualVisitCount, timeCount, ← ENNReal.tsum_mul_left,
    tsum_subtype (Γ.1 ⁻¹' {x})
      (fun t : PathTime => if t ∈ residualTimes B Γ ∧ t ∈ I then m (Γ.1 t) else 0)]
  apply tsum_congr
  intro t
  by_cases he : Γ.1 t = x <;>
    by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ I <;>
      simp [Set.indicator, residualVisitRelation, he, ht]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
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

theorem continuous_tagDataTuple : Continuous tagDataTuple := by
  apply continuous_sigma
  intro n
  exact continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd.fst)

theorem measurable_slotTupleMeasure : Measurable slotTupleMeasure := by
  classical
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let S : Set TagSlot := activeTagSlot '' (tagDataTuple ⁻¹' A)
  have hi : IsOpenEmbedding activeTagSlot := IsOpenEmbedding.inr
  have hme : MeasurableEmbedding activeTagSlot :=
    IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot) hi
  have himg : MeasurableSet S := hme.measurableSet_image.mpr
    (continuous_tagDataTuple.measurable hA)
  have heq : (fun s => slotTupleMeasure s A) = S.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext s
    cases s with
    | inl u =>
      have hnot : (Sum.inl u : TagSlot) ∉ S := by
        rintro ⟨q, _, he⟩
        cases he
      change 0 = if (Sum.inl u : TagSlot) ∈ S then 1 else 0
      rw [ite_eq_right hnot]
    | inr q =>
      have hmem : (Sum.inr q : TagSlot) ∈ S ↔ tagDataTuple q ∈ A := by
        constructor
        · rintro ⟨p, hp, hpq⟩
          cases Sum.inr.inj hpq
          exact hp
        · intro hq
          exact ⟨q, hq, rfl⟩
      change (Measure.dirac (tagDataTuple q)) A = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [Measure.dirac_apply' _ hA]
      change (if tagDataTuple q ∈ A then 1 else 0) = if (Sum.inr q : TagSlot) ∈ S then 1 else 0
      rw [hmem]
  rw [heq]
  exact measurable_const.indicator himg

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem weightedTupleMeasure_apply (θ : ℕ → TagSlot) {s : Set LevelTuple}
    (hs : MeasurableSet s) :
    weightedTupleMeasure θ s = ∑' k, slotWeight k * slotTupleMeasure (θ k) s := by
  simp only [weightedTupleMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

theorem measurable_weightedTupleMeasure : Measurable weightedTupleMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [weightedTupleMeasure_apply _ hs]
  apply Measurable.tsum
  intro k
  exact measurable_const.mul ((Measure.measurable_coe hs).comp
    (measurable_slotTupleMeasure.comp (measurable_pi_apply k)))

theorem weightedTupleMeasure_slot_le (θ : ℕ → TagSlot) (k : ℕ) :
    slotWeight k • slotTupleMeasure (θ k) ≤ weightedTupleMeasure θ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedTupleMeasure_apply θ hs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.le_tsum (f := fun j => slotWeight j * slotTupleMeasure (θ j) s) k

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathVariation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel length data for ordinary continuous metric paths. These are applied
to physical-domain subarcs when forming the path occupation kernel. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_rectifiablePaths :
    MeasurableSet {γ : C(PathTime, X) | BoundedVariationOn γ univ} := by
  change MeasurableSet {γ : C(PathTime, X) | eVariationOn γ univ ≠ ∞}
  exact (measurable_pathVariation univ) (measurableSet_singleton ∞).compl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_pathOccupation : Measurable (pathOccupation (X := X)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have he : Measurable (fun p : RectifiablePath X × PathTime => p.1.val p.2) :=
    (continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).measurable
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := pathLengthKernel (X := X)) (he hs) (fun γ => inferInstance)
  change Measurable (fun γ : RectifiablePath X =>
    pathLengthMeasure γ (γ.val ⁻¹' s)) at hm
  simpa only [pathOccupation_apply _ hs] using hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RectifiableOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Borel occupation code on the Borel subset of rectifiable paths.
The total extension is zero off that subset; length finiteness is always
checked separately before it is used as physical occupation. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_rectifiableOccupationCode :
    Measurable (rectifiableOccupationCode (X := X)) :=
  measurable_pathOccupation.dite measurable_const measurableSet_rectifiablePaths

instance instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology [CompleteSpace X] [SecondCountableTopology X] :
    StandardBorelSpace (RectifiablePath X) :=
  measurableSet_rectifiablePaths.standardBorel

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isOpen_pathsInsideOn {U : Set X} (hU : IsOpen U) (a b : PathTime) :
    IsOpen (pathsInsideOn U a b) :=
  ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hU

theorem continuous_physicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) : Continuous (physicalSubpath e hab) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_subtype_val.comp (e.symm.continuous.comp
    ((continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((timeClip a b).continuous.comp continuous_snd))).subtype_mk _))

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_totalPhysicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (hU : IsOpen U) {a b : PathTime} (hab : a ≤ b) (y₀ : Y) :
    Measurable (totalPhysicalSubpath e hab y₀) := by
  classical
  exact (continuous_physicalSubpath e hab).measurable.dite
    measurable_const (isOpen_pathsInsideOn hU a b).measurableSet

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_IncreasingMeasureLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise increasing limits of the finite-stage occupation measures. -/

open Set MeasureTheory Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y : Type*} [MeasurableSpace Y]

theorem measurable_increasingMeasureLimit {Z : Type*} [MeasurableSpace Z]
    (μ : Z → ℕ → Measure Y) (hμ : ∀ z, Monotone (μ z))
    (hmeas : ∀ n, Measurable (fun z => μ z n)) :
    Measurable (fun z => increasingMeasureLimit (μ z) (hμ z)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [increasingMeasureLimit_apply _ _ hs]
  exact Measurable.iSup fun n => (Measure.measurable_coe hs).comp (hmeas n)

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

theorem measurable_physicalDyadicLength (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n)) : Measurable (physicalDyadicLength e y₀ n i) :=
  (measurable_pathVariation univ).comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀)

theorem measurable_physicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalDomainLength e y₀) := by
  apply Measurable.iSup
  intro n
  exact Finset.measurable_sum _ fun i _ => measurable_physicalDyadicLength e hU y₀ n i

theorem measurableSet_finitePhysicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    MeasurableSet {γ : C(PathTime, X) | physicalDomainLength e y₀ γ < ∞} :=
  measurableSet_lt (measurable_physicalDomainLength e hU y₀) measurable_const

variable [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem physicalStageOccupation_univ (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞) (n : ℕ) :
    physicalStageOccupation e y₀ n γ univ = physicalStageLength e y₀ n γ := by
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableOccupationCode_univ (physicalDyadicPath_rectifiable e y₀ hγ n _)]
  rfl

theorem measurable_physicalStageOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (n : ℕ) :
    Measurable (physicalStageOccupation e y₀ n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro i _
  exact (Measure.measurable_coe hs).comp (measurable_rectifiableOccupationCode.comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀))

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

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_dyadicPhysicalOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (dyadicPhysicalOccupation e y₀) := by
  apply measurable_increasingMeasureLimit
  intro n
  exact (measurable_physicalStageOccupation e hU y₀ n).comp measurable_subtype_coe

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationPushforward
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_physicalValue (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalValue e y₀) :=
  (continuous_subtype_val.comp e.symm.continuous).measurable.dite
    measurable_const hU.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem physicalDyadicLength_map (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) (i : Fin (2 ^ n)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).map
        (physicalValue e y₀ ∘ γ.val) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ.val) := by
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [rectifiableLengthCode_eq hr, rectifiableOccupationCode_eq hr, pathOccupation]
    apply Measure.map_congr
    have hae : ∀ᵐ t ∂pathLengthMeasure
        ⟨physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩, hr⟩,
        t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
      have heq := physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ hr
      rw [rectifiableLengthCode_eq hr] at heq
      rw [heq]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hae] with t ht
    exact physicalValue_subpath e y₀ (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ ht
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi,
      rectifiableLengthCode_const, rectifiableOccupationCode_const]

theorem physicalStageTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (physicalStageTimeLength e y₀ n γ.val).map (physicalValue e y₀ ∘ γ.val) =
      physicalStageOccupation e y₀ n γ.val := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [physicalStageTimeLength, physicalStageOccupation, Measure.coe_finsetSum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← physicalDyadicLength_map e y₀ γ n i, Measure.map_apply hm hs]

theorem physicalTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (physicalTimeLength e y₀ γ).map (physicalValue e y₀ ∘ γ.val) =
      dyadicPhysicalOccupation e y₀ γ := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs, physicalTimeLength_apply _ _ _ (hm hs),
    dyadicPhysicalOccupation_apply _ _ _ hs]
  congr 1
  funext n
  rw [← physicalStageTimeLength_map e hU y₀ γ n, Measure.map_apply hm hs]

theorem physicalOccupation_integral (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ =
      ∫⁻ t, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [← physicalTimeLength_map e hU y₀ γ]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

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

instance instIsFiniteMeasureBaseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : IsFiniteMeasure (baseCodeOccupation d Γ) := by
  unfold baseCodeOccupation
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem measurable_baseCodeOccupation (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) :
    Measurable (baseCodeOccupation d) :=
  (measurable_dyadicPhysicalOccupation d.domainEquiv hU d.basePoint).comp
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual mean occupation, atomic and tuple measures of a law on base
codes. Their sum is exactly the barycenter of the coding measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem measurable_baseCodeTuple (d : PathCodeData X Y) :
    Measurable (fun Γ : BasePathCode d => weightedTupleMeasure Γ.val.2) :=
  measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem meanCodeOccupation_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set Y} (hA : MeasurableSet A) :
    meanCodeOccupation d P A = ∫⁻ Γ, baseCodeOccupation d Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeOccupation d hU).aemeasurable

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem meanCodeTuple_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    meanCodeTuple d P A = ∫⁻ Γ, weightedTupleMeasure Γ.val.2 A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeTuple d).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotLawMeasures
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each fixed slot distribution is dominated by the mean weighted tuple
measure, and hence inherits its absolute continuity. Inactive slots have
zero mass, so these are subprobability measures. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem measurable_baseCodeSlot (d : PathCodeData X Y) (k : ℕ) :
    Measurable (baseCodeSlot d k) :=
  measurable_slotTupleMeasure.comp
    ((measurable_pi_apply k).comp (measurable_snd.comp measurable_subtype_coe))

theorem slotLaw_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) {A : Set LevelTuple} (hA : MeasurableSet A) :
    slotLaw d P k A = ∫⁻ Γ, slotTupleMeasure (Γ.val.2 k) A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeSlot d k).aemeasurable

theorem weighted_slotLaw_le (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (k : ℕ) : slotWeight k • slotLaw d P k ≤ meanCodeTuple d P := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul, slotLaw_apply d P k hA, meanCodeTuple_apply d P hA]
  have hm : Measurable (fun Γ : BasePathCode d => slotTupleMeasure (Γ.val.2 k) A) :=
    (Measure.measurable_coe hA).comp (measurable_baseCodeSlot d k)
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono
  intro Γ
  have h := (Measure.le_iff.mp (weightedTupleMeasure_slot_le Γ.val.2 k)) A hA
  simpa only [Measure.smul_apply, smul_eq_mul] using h

theorem slotLaw_absolutelyContinuous (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (k : ℕ) : slotLaw d P k ≪ τ :=
  (Measure.absolutelyContinuous_smul (slotWeight_pos k).ne').trans
    ((weighted_slotLaw_le d P k).absolutelyContinuous.trans hτ)

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

theorem countingSquareNorm_mono {D : Type*} {a b : D → ℝ≥0∞}
    (h : ∀ s, a s ≤ b s) : countingSquareNorm a ≤ countingSquareNorm b := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact ENNReal.tsum_le_tsum (fun s => pow_le_pow_left' (h s) 2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ResidualTailNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite deletion constraints exclude residual incidences off the support
of the toll whenever the actual full path toll is finite. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_deleted_series_zero {A : Type*} [Countable A]
    (f : A → ℝ≥0∞) (hf : (∑' a, f a) ≠ ∞) (P : ℕ → Set A)
    (hP : ∀ a, ∀ᶠ n in atTop, a ∈ P n) :
    Tendsto (fun n => ∑' a, if a ∈ P n then 0 else f a) atTop (𝓝 0) := by
  let : MeasurableSpace A := ⊤
  have h := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
    (F := fun n a => if a ∈ P n then 0 else f a) (f := fun _ => 0) f
    (fun _ => measurable_of_countable _)
    (fun n => Eventually.of_forall fun a => by
      change (if a ∈ P n then 0 else f a) ≤ f a
      split_ifs <;> simp)
    (by simpa only [lintegral_count] using hf)
    (Eventually.of_forall fun a => tendsto_const_nhds.congr' ((hP a).mono fun n hn => by simp [hn]))
  simpa only [lintegral_count, tsum_zero] using h

variable {X : Type*} [MetricSpace X]

theorem residualVisitCount_le_visitCount (B : Set X) (I : Set PathTime)
    (Γ : TaggedPath X) (x : X) : residualVisitCount B I Γ x ≤ visitCount Γ.1 x := by
  rw [residualVisitCount, timeCount, visitCount_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases h : (Γ.1 t = x)
  · simp only [h, ite_true, if_true]
    split_ifs <;> simp
  · have hn : ((Γ, x), t) ∉ residualVisitRelation B I := fun hh => h hh.2.2
    simp only [h, hn, ite_false, if_false, le_refl]

theorem residualToll_deleted_le (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (P : Set X) (Γ : TaggedPath X) :
    residualToll B I (deletedWeight P m) Γ ≤
      ∑' x : support m, if x.val ∈ P then 0 else m x.val * visitCount Γ.1 x.val := by
  rw [residualToll_eq_visits]
  have he : (∑' x, deletedWeight P m x * residualVisitCount B I Γ x) =
      ∑' x : support m, deletedWeight P m x.val * residualVisitCount B I Γ x.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun x : X => deletedWeight P m x * residualVisitCount B I Γ x)
    intro x hx
    by_contra hn
    have hz : m x = 0 := notMem_support.mp hn
    simp [deletedWeight, hz] at hx
  rw [he]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x.val ∈ P
  · simp [deletedWeight, hx]
  · simpa only [deletedWeight, hx, ite_false, if_false] using
      mul_le_mul' (le_refl (m x.val)) (residualVisitCount_le_visitCount B I Γ x.val)

theorem residual_incidence_envelope_null {Z : Type*} [MeasurableSpace Z]
    (B : Set X) (I : Set PathTime) (R : Set (Z × X)) (ν : Measure Z)
    (m : X → ℝ≥0∞) (hm : (support m).Countable) (P : ℕ → Set X)
    (hcover : ∀ x ∈ support m, ∀ᶠ n in atTop, x ∈ P n)
    (Γ : TaggedPath X) (hfinite : boundaryToll Γ.1 m < ∞)
    (hbound : ∀ n, ResidualIncidenceBound B I R (P n) ν m Γ) :
    ν (⋂ n, {z | (Γ, z) ∈ residualIncidence B I R (P n)}) = 0 := by
  let : Countable (support m) := hm.to_subtype
  have ht := tendsto_deleted_series_zero
    (fun x : support m => m x.val * visitCount Γ.1 x.val)
    (by simpa only [← boundaryToll_eq_support] using hfinite.ne)
    (fun n => {x : support m | x.val ∈ P n})
    (fun x => hcover x.val x.property)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro n
  exact (measure_mono (iInter_subset _ n)).trans
    ((hbound n).trans (residualToll_deleted_le B I m (P n) Γ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SquareVisitTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square bounds on weights and mean visits give finite actual weighted
tolls almost surely. This retains all visits, including both endpoints. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

theorem tsum_mul_le_countingSquareNorm {A : Type*} [Countable A]
    (a b : A → ℝ≥0∞) :
    (∑' x, a x * b x) ≤ countingSquareNorm a * countingSquareNorm b := by
  let : MeasurableSpace A := ⊤
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := Measure.count)
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by constructor <;> norm_num)
    (measurable_of_countable a).aemeasurable (measurable_of_countable b).aemeasurable
  simpa only [Pi.mul_apply, ENNReal.rpow_two, lintegral_count, countingSquareNorm] using h

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem lintegral_boundaryToll_le_square_norms (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable) :
    (∫⁻ γ, boundaryToll γ m ∂(μ : Measure _)) ≤
      countingSquareNorm (fun x : support m => m x.val) *
      countingSquareNorm (fun x : support m => meanVisitCount μ x.val) := by
  let : Countable (support m) := hm.to_subtype
  rw [lintegral_boundaryToll μ hm]
  exact tsum_mul_le_countingSquareNorm _ _

theorem ae_boundaryToll_finite (μ : ProbabilityMeasure C(PathTime, X))
    (m : X → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), boundaryToll γ m < ∞ := by
  apply ae_lt_top (measurable_boundaryToll hm)
  exact ((lintegral_boundaryToll_le_square_norms μ m hm).trans_lt
    (ENNReal.mul_lt_top hweight hvisits)).ne

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CodeResidualAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The stored rational-interval constraints give null residual-incidence
envelopes under the actual square bounds on visits. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

private theorem rationalStart_eq : rationalStart.toTime = (⊥ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalStart, RationalPathTime.toTime]

private theorem rationalEnd_eq : rationalEnd.toTime = (⊤ : PathTime) := by
  apply Subtype.ext
  norm_num [rationalEnd, RationalPathTime.toTime]

theorem baseCode_level_bound (d : PathCodeData X Y) (Γ : BasePathCode d) (i n : ℕ) :
    ResidualIncidenceBound d.dust univ (d.levels i) (d.flagDeletions n)
      volume (d.levelWeights i) Γ.val := by
  have h := Γ.property.1.2.2.2.1 i n rationalStart rationalEnd
  simpa only [rationalStart_eq, rationalEnd_eq, Icc_bot_top] using h

variable [BorelSpace X] [SecondCountableTopology X] [BorelSpace C(PathTime, X)]

theorem ae_code_boundaryToll_finite (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (m : X → ℝ≥0∞)
    (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), boundaryToll Γ.val.1 m < ∞ := by
  have h := ae_boundaryToll_finite (codePathLaw d P) m hm hweight hvisits
  exact (ae_map_iff (measurable_codePath d).aemeasurable
    (measurableSet_lt (measurable_boundaryToll hm) measurable_const)).mp h

theorem ae_code_level_envelope_null (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i),
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), volume
      (⋂ n, {t | (Γ.val, t) ∈ residualIncidence d.dust univ (d.levels i)
        (d.flagDeletions n)}) = 0 := by
  filter_upwards [ae_code_boundaryToll_finite d P _ hm hweight hvisits] with Γ hΓ
  exact residual_incidence_envelope_null d.dust univ (d.levels i) _ _ hm _ hcover
    Γ.val hΓ (baseCode_level_bound d Γ i)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_CodeFreeTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual constraints stored in a base code combine with the
open-tag trace theorem to exclude free incidences along the entire path.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_free_level_incidence_null
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set X) (hFree : Free ⊆ d.dust) (w : X → UnitAddCircle)
    (htrace : ∀ x ∈ Free, ∀ t, (t, x) ∈ d.levels i ↔ w x = t)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set X))
    (htags : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume (w '' (Γ.val.1 '' Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Free)) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {t | ∃ x ∈ range Γ.val.1 ∩ Free, (t, x) ∈ d.levels i} = 0 := by
  filter_upwards [ae_code_level_envelope_null d P i hm hweight hvisits hcover, htags]
    with Γ hres htag
  have hresidual : volume (w '' (Γ.val.1 '' residualTimes d.dust Γ.val ∩ Free)) = 0 := by
    apply measure_mono_null (t := ⋂ n, {t | (Γ.val, t) ∈
      residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}) _ hres
    rintro _ ⟨x, ⟨⟨s, hs, rfl⟩, hx⟩, rfl⟩
    exact mem_iInter.mpr fun n => ⟨s, hs, mem_univ _,
      (htrace _ hx _).mpr rfl, fun hp => disjoint_left.mp (hdelete n) hx hp⟩
  exact free_level_incidence_null_of_trace volume Γ.val.1 Free w (d.levels i)
    (fun x hx t ht => (htrace x hx t).mp ht)
    (tagged_free_trace_null d.dust Free hFree Γ.val w hresidual htag)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CodeFreeIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining the actual residual constraints with null incidence sets
on the open tags needs no globally chosen circle trace. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_free_level_incidence_null_of_tags
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set X) (hFree : Free ⊆ d.dust)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set X))
    (htags : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume {θ | ∃ t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)),
        Γ.val.1 t ∈ Free ∧ (θ, Γ.val.1 t) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ Free, (θ, x) ∈ d.levels i} = 0 := by
  filter_upwards [ae_code_level_envelope_null d P i hm hweight hvisits hcover, htags]
    with Γ hres htag
  apply measure_mono_null (t :=
    (⋂ n, {θ | (Γ.val, θ) ∈ residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}) ∪
    ⋃ k, {θ | ∃ t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)),
      Γ.val.1 t ∈ Free ∧ (θ, Γ.val.1 t) ∈ d.levels i}) _
    (measure_union_null hres (measure_iUnion_null htag))
  rintro θ ⟨x, ⟨⟨t, rfl⟩, hx⟩, hθ⟩
  by_cases ht : ∃ k, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k))
  · obtain ⟨k, hk⟩ := ht
    exact Or.inr (mem_iUnion.mpr ⟨k, t, hk, hx, hθ⟩)
  · apply Or.inl
    apply mem_iInter.mpr
    intro n
    refine ⟨t, ?_, mem_univ _, hθ, fun hp => disjoint_left.mp (hdelete n) hx hp⟩
    rw [residualTimes_eq]
    exact ⟨hFree hx, fun h => ht (mem_iUnion.mp h)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathHausdorffLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
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
-- module Solutions.Q146_CD.CircleDomains_Probability_PathImageOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hausdorff measure of a path image counts each point once; arclength
occupation counts every traversal. Compact time sets and fine dyadic covers
prove the resulting measure domination without an injectivity assumption. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

lemma eventually_dyadic_cells_inside_compact {K V : Set PathTime}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ K).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hd⟩ := hK.exists_thickening_subset_open hV hKV
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  filter_upwards [(tendsto_order.mp hz).2 δ hδ] with n hn i hi t ht
  obtain ⟨s, hs, hsK⟩ := hi
  exact hd (mem_thickening_iff.mpr ⟨s, hsK, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩)

lemma exists_small_dyadic_images_ge {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  obtain ⟨n, hn, hN⟩ := (((tendsto_order.mp hz).2 δ hδ).and (eventually_ge_atTop N)).exists
  refine ⟨n, hN, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma path_hausdorff_image_compact_le_open (γ : RectifiablePath X)
    {K V : Set PathTime} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ V := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  choose k hkn hk using fun n => exists_small_dyadic_images_ge γ.val (hr n) n
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ.val '' (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K)
  have hcover (n : ℕ) : γ.val '' K ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, ⟨hi, ht⟩, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hfine : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ k n),
      (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty →
      Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ⊆ V :=
    (tendsto_atTop_mono hkn tendsto_id).eventually
      (eventually_dyadic_cells_inside_compact hK hV hKV)
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (γ.val '' K)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall fun n i => (ediam_mono (image_mono inter_subset_left)).trans (hk n i))
    (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hfine] with n hn
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤ ∑ i : Fin (2 ^ k n),
        (pathLengthMeasure γ).restrict (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) V := by
      apply Finset.sum_le_sum
      intro i _
      rw [Measure.restrict_apply hV.measurableSet]
      by_cases hi : (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i) ∩ K).Nonempty
      · rw [inter_eq_self_of_subset_right (hn i hi), pathLengthMeasure_Icc γ (dyadicLeft_le_right _ _)]
        apply ediam_le
        rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
        exact eVariationOn.edist_le γ.val hs.1 ht.1
      · have he : A n i = ∅ := by simp only [A, not_nonempty_iff_eq_empty.mp hi, image_empty]
        rw [he, ediam_empty]
        exact bot_le
    _ = pathLengthMeasure γ V := by
      rw [← Measure.finsetSum_apply, sum_dyadic_restrict]

lemma path_hausdorff_image_compact_le_length (γ : RectifiablePath X)
    {K : Set PathTime} (hK : IsCompact K) :
    (μH[1] : Measure X) (γ.val '' K) ≤ pathLengthMeasure γ K := by
  rw [K.measure_eq_iInf_isOpen (pathLengthMeasure γ)]
  exact le_iInf fun V => le_iInf fun hKV => le_iInf fun hV =>
    path_hausdorff_image_compact_le_open γ hK hV hKV

/-- A curve's occupation dominates Hausdorff measure on its image, even
when the curve retraces itself. -/
theorem path_image_hausdorff_le_occupation (γ : RectifiablePath X) :
    (μH[1] : Measure X).restrict (range γ.val) ≤ pathOccupation γ := by
  let ν := (μH[1] : Measure X).restrict (range γ.val)
  have hfin : ν univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (path_hausdorff_length_le_variation γ.val).trans_lt (lt_top_iff_ne_top.mpr γ.property)
  let : IsFiniteMeasure ν := ⟨hfin⟩
  apply Measure.le_iff.mpr
  intro S hS
  change ν S ≤ pathOccupation γ S
  rw [hS.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top ν S)]
  apply iSup_le
  intro F
  apply iSup_le
  intro hFS
  apply iSup_le
  intro hF
  apply le_trans ?_ (measure_mono hFS)
  change (μH[1] : Measure X).restrict (range γ.val) F ≤ pathOccupation γ F
  rw [Measure.restrict_apply hF.measurableSet, pathOccupation_apply γ hF.measurableSet]
  have he : F ∩ range γ.val = γ.val '' (γ.val ⁻¹' F) := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_image, mem_preimage]
    aesop
  rw [he]
  exact path_hausdorff_image_compact_le_length γ (hF.preimage γ.val.continuous).isCompact

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalImageOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General physical paths pay for the Hausdorff measure of their images.
Together with the opposite simple-arc bound this makes erasing loops decrease
physical occupation, including for arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalSubpath_range (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X))
    {a b : PathTime} (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    range (physicalSubpath e hab ⟨γ, hγ⟩) =
      (physicalValue e y₀ ∘ γ) '' Icc a b := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    exact ((congrArg (fun f : C(PathTime, Y) => f t)
      (physicalSubpath_comp_clip e hab ⟨γ, hγ⟩)).symm).trans
        (physicalValue_subpath e y₀ hab ⟨γ, hγ⟩ ht).symm
  rw [he, range_comp, range_timeClip hab]

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalStageImage_subset (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (n : ℕ) :
    physicalStageImage e y₀ γ n ⊆ (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · exact image_mono hgood hi
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma monotone_physicalStageImage (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    Monotone (physicalStageImage e y₀ γ) := by
  apply monotone_nat_of_le_succ
  intro n y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · obtain ⟨t, ht, rfl⟩ := hi
    rw [dyadicCell_split] at ht
    rcases ht with ht | ht
    · apply mem_iUnion.mpr
      refine ⟨dyadicEven n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicEven n i))
          (dyadicRight (n+1) (dyadicEven n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_left
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
    · apply mem_iUnion.mpr
      refine ⟨dyadicOdd n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicOdd n i))
          (dyadicRight (n+1) (dyadicOdd n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_right
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma iUnion_physicalStageImage (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : C(PathTime, X)) :
    (⋃ n, physicalStageImage e y₀ γ n) = (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  apply Subset.antisymm (iUnion_subset (physicalStageImage_subset e y₀ γ))
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨p, hp⟩ := mem_iUnion.mp ((iUnion_insideDyadicCell (hU.preimage γ.continuous)).symm ▸ ht)
  apply mem_iUnion.mpr
  refine ⟨p.val.1, mem_iUnion.mpr ⟨p.val.2, ?_⟩⟩
  have hg : γ ∈ pathsInsideOn U (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2) := p.property
  rw [ite_eq_left hg]
  exact ⟨t, hp, rfl⟩

lemma physicalStageImage_hausdorff_le (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (μH[1] : Measure Y).restrict (physicalStageImage e y₀ γ.val n) ≤
      physicalStageOccupation e y₀ n γ.val := by
  unfold physicalStageImage physicalStageOccupation
  apply le_trans Measure.restrict_iUnion_le
  rw [Measure.sum_fintype]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · rw [ite_eq_left hi]
    have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [← physicalSubpath_range e y₀ γ.val (dyadicLeft_le_right n i) hi,
      rectifiableOccupationCode_eq hr]
    exact path_image_hausdorff_le_occupation ⟨_, hr⟩
  · rw [ite_eq_right hi, Measure.restrict_empty]
    exact bot_le

theorem physical_image_hausdorff_le_occupation (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) ≤
      dyadicPhysicalOccupation e y₀ γ := by
  rw [← iUnion_physicalStageImage e hU y₀ γ.val]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_iUnion_apply_eq_iSup (monotone_physicalStageImage e y₀ γ.val).directed_le hS,
    dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_mono fun n => physicalStageImage_hausdorff_le e y₀ γ n S

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel physical occupation on ordinary path space, with zero extension
off the finite-length paths. This lets measurable arc selection act directly
on path laws without introducing a new code law. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

lemma physicalOccupationCode_eq (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    physicalOccupationCode e y₀ γ.val = dyadicPhysicalOccupation e y₀ γ := by
  simp only [physicalOccupationCode, dite_eq_left γ.property]

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

lemma measurable_physicalOccupationCode (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalOccupationCode e y₀) := by
  have hm := (measurable_dyadicPhysicalOccupation e hU y₀).dite
    (show Measurable (fun _ => (0 : Measure Y)) from measurable_const)
    (measurableSet_finitePhysicalDomainLength e hU y₀)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext γ
  unfold physicalOccupationCode
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

lemma meanPhysicalOccupation_apply (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) {S : Set Y} (hS : MeasurableSet S) :
    meanPhysicalOccupation e y₀ μ S =
      ∫⁻ γ, physicalOccupationCode e y₀ γ S ∂(μ : Measure C(PathTime, X)) :=
  Measure.bind_apply hS (measurable_physicalOccupationCode e hU y₀).aemeasurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CodeLawPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forgetting tags preserves the actual mean physical occupation. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_1 : BorelSpace Sphere := ⟨rfl⟩
theorem meanPhysicalOccupation_codePathLaw (d : PathCodeData Sphere Sphere)
    (hU : IsOpen d.quotientDomain) (P : ProbabilityMeasure (BasePathCode d)) :
    meanPhysicalOccupation d.domainEquiv d.basePoint (codePathLaw d P) =
      meanCodeOccupation d P := by
  apply Measure.ext
  intro S hS
  have hm : Measurable (fun γ => physicalOccupationCode d.domainEquiv d.basePoint γ S) :=
    (Measure.measurable_coe hS).comp (measurable_physicalOccupationCode d.domainEquiv hU d.basePoint)
  rw [meanPhysicalOccupation_apply _ hU _ _ hS, meanCodeOccupation_apply d hU P hS,
    codePathLaw, ProbabilityMeasure.toMeasure_map, lintegral_map hm (measurable_codePath d)]
  apply lintegral_congr
  intro Γ
  exact congrArg (fun ν : Measure Sphere => ν S)
    (physicalOccupationCode_eq d.domainEquiv d.basePoint (baseCodePhysicalPath d Γ))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical costs are integrals against the actual mean
occupation. Square bounds on the density, differential and visit weights
give the finite costs needed for the parameter-time payment measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem lintegral_physicalOccupationCode (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ γ, ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ ∂(μ : Measure _)) =
      ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ := by
  exact (Measure.lintegral_bind (measurable_physicalOccupationCode e hU y₀).aemeasurable
    hg.aemeasurable).symm

theorem lintegral_physical_cost_le_square_norms (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ) :
    (∫⁻ γ, ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ ∂(μ : Measure _)) ≤
      (∫⁻ y, ρ y ^ 2 ∂σ) ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ 2 ∂σ) ^ (1 / 2 : ℝ) := by
  rw [lintegral_physicalOccupationCode e hU y₀ μ g hg, hocc,
    lintegral_withDensity_eq_lintegral_mul _ hρ hg]
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  simpa only [Pi.mul_apply, ENNReal.rpow_two] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hρ.aemeasurable hg.aemeasurable

theorem ae_physical_cost_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂σ) < ∞) (hg2 : (∫⁻ y, g y ^ 2 ∂σ) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) < ∞ := by
  apply ae_lt_top ((Measure.measurable_lintegral hg).comp
    (measurable_physicalOccupationCode e hU y₀))
  exact ((lintegral_physical_cost_le_square_norms e hU y₀ μ σ ρ g hρ hg hocc).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hρ2.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg2.ne))).ne

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem ae_physical_and_visit_cost_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂σ) < ∞) (hg2 : (∫⁻ y, g y ^ 2 ∂σ) < ∞)
    (m : X → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _),
      (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) + boundaryToll γ m < ∞ := by
  filter_upwards [ae_physical_cost_finite e hU y₀ μ σ ρ g hρ hg hocc hρ2 hg2,
    ae_boundaryToll_finite μ m hm hweight hvisits] with γ hγ hγ'
  exact ENNReal.add_lt_top.mpr ⟨hγ, hγ'⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffinePhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical costs of restricted paths are the old costs on the
retained interval, with full multiplicity and no endpoint atoms. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalOccupation_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (physicalValue e y₀ ∘ γ.val) := by
  have hf := (measurable_physicalValue e hU y₀).comp
    (affineRestrictedPath a b γ.val).continuous.measurable
  rw [← physicalTimeLength_map e hU y₀, physicalTimeLength_affine e hU y₀ γ hab]
  change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (physicalValue e y₀ ∘ affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map hf (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change physicalValue e y₀ (γ.val (affinePathTime a b (rescalePathTime a b t))) =
    physicalValue e y₀ (γ.val t)
  rw [affine_rescalePathTime hab ht]

theorem physicalCost_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab)) =
      ∫⁻ t in Icc a b, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [physicalOccupation_affine e hU y₀ γ hab]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_IntervalPaymentNullImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite payment measure that vanishes on free times forces their
trace image to be null, once interval oscillation is paid. This is the
last measure-theoretic step of the local tag argument. -/

open Set MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

private theorem locallyConnected_pathTime_p0 : LocallyConnectedSpace PathTime := by
  apply locallyConnectedSpace_of_connected_bases
    (fun x r => Metric.ball x r) (fun _ r => 0 < r)
    (fun _ => Metric.nhds_basis_ball)
  intro x r _
  apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
  rw [Subtype.image_ball, Real.ball_eq_Ioo]
  exact (ordConnected_Ioo.inter ordConnected_Icc).isPreconnected

theorem path_time_null_image_of_interval_payment
    (κ : Measure PathTime) [IsFiniteMeasure κ] [κ.OuterRegular]
    {F V : Set PathTime} (hV : IsOpen V) (hF : κ (F ∩ V) = 0)
    (v : PathTime → ℝ)
    (hpay : ∀ r ∈ F ∩ V, ∀ s ∈ F ∩ V, r ≤ s → Icc r s ⊆ V →
      ENNReal.ofReal |v s - v r| ≤ κ (Icc r s)) :
    volume (v '' (F ∩ V)) = 0 := by
  let : LocallyConnectedSpace PathTime := locallyConnected_pathTime_p0
  apply null_image_inter_open_of_connected_open_oscillation hV hF v (A := 1) zero_le_one
  intro U hUV _ hconn r hr s hs
  have hforward : ∀ p ∈ F ∩ U, ∀ q ∈ F ∩ U, p ≤ q →
      |v q - v p| ≤ κ.real U := by
    intro p hp q hq hpq
    have hi : Icc p q ⊆ U := hconn.isPreconnected.ordConnected.out hp.2 hq.2
    have h := hpay p ⟨hp.1, hUV hp.2⟩ q ⟨hq.1, hUV hq.2⟩ hpq (hi.trans hUV)
    have hreal := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top κ (Icc p q))).mp h
    exact hreal.trans (measureReal_mono hi)
  rw [one_mul]
  rcases le_total r s with h | h
  · simpa only [abs_sub_comm] using hforward r hr s hs h
  · exact hforward s hs r hr h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagPaymentMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local tag cost is an actual measure on parameter time: a
weighted physical-length part plus one atom for each flagged visit. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem boundaryTimeMeasure_apply {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞)
    {S : Set PathTime} (hS : MeasurableSet S) :
    boundaryTimeMeasure γ m S = ∑' t, m (γ t) * S.indicator 1 t := by
  simp only [boundaryTimeMeasure, Measure.sum_apply _ hS, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hS]

theorem boundaryTimeMeasure_univ {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryTimeMeasure γ m univ = boundaryToll γ m := by
  simp only [boundaryTimeMeasure_apply γ m MeasurableSet.univ, indicator_univ,
    Pi.one_apply, mul_one, boundaryToll]

theorem tagPaymentMeasure_univ {X : Type*} [MetricSpace X]
    (μ : Measure PathTime) (g : PathTime → ℝ≥0∞)
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    tagPaymentMeasure μ g γ m univ = (∫⁻ t, g t ∂μ) + boundaryToll γ m := by
  rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, boundaryTimeMeasure_univ]

theorem tagPaymentMeasure_null_free {X : Type*}
    (μ : Measure PathTime) (g : PathTime → ℝ≥0∞) (γ : PathTime → X) (m : X → ℝ≥0∞)
    {F : Set PathTime} (hF : MeasurableSet F) (hμ : μ F = 0)
    (hm : ∀ t ∈ F, m (γ t) = 0) :
    tagPaymentMeasure μ g γ m F = 0 := by
  rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ hF,
    Measure.restrict_eq_zero.mpr hμ, lintegral_zero_measure, zero_add,
    boundaryTimeMeasure_apply γ m hF]
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  by_cases ht : t ∈ F
  · rw [hm t ht, zero_mul]
  · simp only [indicator_of_notMem ht, mul_zero]

/-- Paying once at each distinct image point is bounded by paying at every visit. -/
theorem boundaryTimeMeasure_image_le {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞)
    {S : Set PathTime} (hS : MeasurableSet S) {A : Set X} (hA : A ⊆ γ '' S) :
    (∑' x : A, m x.val) ≤ boundaryTimeMeasure γ m S := by
  classical
  choose τ hτ hγ using fun x : A => hA x.property
  have hinj : Function.Injective τ := by
    intro x y hxy
    apply Subtype.ext
    exact (hγ x).symm.trans ((congrArg γ hxy).trans (hγ y))
  rw [boundaryTimeMeasure_apply γ m hS]
  calc
    (∑' x : A, m x.val) = ∑' x : A, m (γ (τ x)) * S.indicator 1 (τ x) := by
      apply tsum_congr
      intro x
      simp only [hγ x, indicator_of_mem (hτ x), Pi.one_apply, mul_one]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun t => m (γ t) * S.indicator 1 t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalTagPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local payment measure is formed from actual physical time length
and the flagged visit toll. Its total mass is bounded by the selected
path law’s cost. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalTagPayment_univ (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g)
    (m : X → ℝ≥0∞) :
    physicalTagPayment e y₀ γ g m univ =
      (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ) + boundaryToll γ.val m := by
  rw [physicalTagPayment, tagPaymentMeasure_univ, physicalOccupation_integral e hU y₀ γ g hg]

theorem physicalTagPayment_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g)
    (m : X → ℝ≥0∞)
    (hcost : (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ) + boundaryToll γ.val m < ∞) :
    IsFiniteMeasure (physicalTagPayment e y₀ γ g m) := by
  constructor
  rwa [physicalTagPayment_univ e hU y₀ γ g hg m]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem physicalTagPayment_null_free (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    {F : Set PathTime} (hF : MeasurableSet F) (hout : ∀ t ∈ F, γ.val t ∉ U)
    (hm : ∀ t ∈ F, m (γ.val t) = 0) :
    physicalTagPayment e y₀ γ g m F = 0 := by
  apply tagPaymentMeasure_null_free _ _ _ _ hF _ hm
  exact measure_mono_null hout (physicalTimeLength_compl e hU y₀ γ)

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

theorem ae_real_interval_of_ae_circle (P : UnitAddCircle → Prop)
    (hP : ∀ᵐ t : UnitAddCircle ∂volume, P t) (a : ℝ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioc a (a + 1)), P (r : UnitAddCircle) :=
  (AddCircle.measurePreserving_mk (1 : ℝ) a).quasiMeasurePreserving.ae hP

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ThresholdImagePayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the paid-threshold cover gives the local image payment.
The bands here are the actual compact real fibers. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

theorem interval_payment_of_ae_cover {I : Type*} [Countable I]
    (S : Set ℝ) (T : I → Set ℝ) (a b : ℝ)
    (hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      t ∈ S ∨ ∃ i, t ∈ T i) :
    ENNReal.ofReal (b - a) ≤ volume S + ∑' i, volume (T i) := by
  have hsub : ∀ᵐ t : ℝ ∂volume, t ∈ Ioo a b → t ∈ S ∪ ⋃ i, T i := by
    have h := (ae_restrict_iff' measurableSet_Ioo).mp hcover
    filter_upwards [h] with t ht htab
    rcases ht htab with hs | ⟨i, hi⟩
    · exact Or.inl hs
    · exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
  calc
    ENNReal.ofReal (b - a) = volume (Ioo a b) := (Real.volume_Ioo).symm
    _ ≤ volume (S ∪ ⋃ i, T i) := measure_mono_ae hsub
    _ ≤ volume S + volume (⋃ i, T i) := measure_union_le _ _
    _ ≤ volume S + ∑' i, volume (T i) := add_le_add le_rfl (measure_iUnion_le _)

theorem real_band_fiber_volume
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} (hx : x ∈ closure D) :
    volume {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph D f)} =
      ENNReal.ofReal (limsup f (𝓝[D] x) - liminf f (𝓝[D] x)) := by
  rw [intervalFiberHull_clusterGraph_eq_boundary_band hM hx, Real.volume_Icc]

theorem interval_band_payment_of_ae_cover
    {X I : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X] [Countable I]
    {D : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    (s : I → X) (hs : ∀ i, s i ∈ closure D) (S : Set ℝ) (a b : ℝ)
    (hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
      t ∈ S ∨ ∃ i, (s i, t) ∈ intervalFiberHull (clusterGraph D f)) :
    ENNReal.ofReal (b - a) ≤ volume S +
      ∑' i, ENNReal.ofReal (limsup f (𝓝[D] (s i)) - liminf f (𝓝[D] (s i))) := by
  have h := interval_payment_of_ae_cover S
    (fun i => {t | (s i, t) ∈ intervalFiberHull (clusterGraph D f)}) a b hcover
  simpa only [real_band_fiber_volume hM (hs _)] using h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactBandCrossing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact graph with nonempty interval fibers has the intermediate
value property along connected sets. This supplies the sign separation
argument for the closed coordinate bands, including at dust points. -/

open Set

noncomputable section
namespace CircleDomainRigidity

theorem compact_band_crossing
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) {C : Set X}
    (hC : IsPreconnected C)
    (hne : ∀ x ∈ C, {t : ℝ | (x, t) ∈ K}.Nonempty)
    (hinterval : ∀ x ∈ C, OrdConnected {t : ℝ | (x, t) ∈ K})
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) {a b v : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b) :
    ∃ z ∈ C, (z, v) ∈ K := by
  let L := Prod.fst '' (K ∩ {p : X × ℝ | p.2 ≤ v})
  let R := Prod.fst '' (K ∩ {p : X × ℝ | v ≤ p.2})
  have hL : IsClosed L :=
    ((hK.inter_right (isClosed_le continuous_snd continuous_const)).image continuous_fst).isClosed
  have hR : IsClosed R :=
    ((hK.inter_right (isClosed_le continuous_const continuous_snd)).image continuous_fst).isClosed
  have hcover : C ⊆ L ∪ R := by
    intro z hz
    obtain ⟨t, ht⟩ := hne z hz
    rcases le_total t v with h | h
    · exact Or.inl ⟨(z, t), ⟨ht, h⟩, rfl⟩
    · exact Or.inr ⟨(z, t), ⟨ht, h⟩, rfl⟩
  obtain ⟨z, hz, hzL, hzR⟩ := (isPreconnected_closed_iff.mp hC) L R hL hR hcover
    ⟨x, hx, (x, a), ⟨ha, hav⟩, rfl⟩ ⟨y, hy, (y, b), ⟨hb, hvb⟩, rfl⟩
  obtain ⟨⟨z₁, u⟩, ⟨hu, huv⟩, he₁⟩ := hzL
  obtain ⟨⟨z₂, w⟩, ⟨hw, hvw⟩, he₂⟩ := hzR
  change z₁ = z at he₁
  change z₂ = z at he₂
  subst z₁
  subst z₂
  exact ⟨z, hz, (hinterval z hz).out hu hw ⟨huv, hvw⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathBoundaryDetour
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing all visits to one open disk by a boundary path. The new
path introduces no points except on the boundary and removes every
interior visit. This is the path surgery used for singleton contacts. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_first_closed_visit
    {X : Type*} [TopologicalSpace X] (γ : C(PathTime, X))
    {U : Set X} (hU : IsOpen U) (hstart : γ ⊥ ∉ closure U)
    (hvisit : (range γ ∩ U).Nonempty) :
    ∃ a : PathTime, γ a ∈ frontier U ∧ ∀ t ≤ a, γ t ∉ U := by
  let T : Set PathTime := γ ⁻¹' closure U
  have hT : IsCompact T := (isClosed_closure.preimage γ.continuous).isCompact
  have hne : T.Nonempty := by
    obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hvisit
    exact ⟨t, subset_closure hz⟩
  let a := sInf T
  have ha : γ a ∈ closure U := hT.sInf_mem hne
  have hpos : ⊥ < a := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    exact hstart (he ▸ ha)
  have hbefore : MapsTo γ (Iio a) (closure U)ᶜ := by
    intro t ht hm
    exact ht.not_ge (sInf_le (show t ∈ T from hm))
  have hcl : a ∈ closure (Iio a) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : a ≤ a)
  have hnot : γ a ∉ U :=
    (closure_minimal (compl_subset_compl.mpr (subset_closure : U ⊆ closure U))
      hU.isClosed_compl) (hbefore.closure γ.continuous hcl)
  refine ⟨a, ?_, ?_⟩
  · rw [hU.frontier_eq]
    exact ⟨ha, hnot⟩
  · intro t ht
    rcases ht.eq_or_lt with rfl | hlt
    · exact hnot
    · exact fun hm => hbefore hlt (subset_closure hm)

private theorem joinedIn_initial_without_open
    {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (U : Set X) (a : PathTime) (ha : ∀ t ≤ a, γ t ∉ U) :
    JoinedIn (range γ \ U) x (γ a) := by
  have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
  have h1 : (1 : PathTime) = ⊤ := Subtype.ext rfl
  let α : Path x (γ a) := {
    toFun := γ ∘ affinePathTime ⊥ a
    continuous_toFun := γ.continuous.comp (affinePathTime ⊥ a).continuous
    source' := by
      change γ (affinePathTime ⊥ a (0 : PathTime)) = x
      rw [h0, affinePathTime_zero, ← h0, Path.source]
    target' := by
      change γ (affinePathTime ⊥ a (1 : PathTime)) = γ a
      rw [h1, affinePathTime_one] }
  refine ⟨α, ?_⟩
  intro t
  exact ⟨mem_range_self _, ha _ (affinePathTime_mem_Icc bot_le t).2⟩

theorem exists_boundary_detour
    {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {U : Set X} (hU : IsOpen U) (hx : x ∉ closure U) (hy : y ∉ closure U)
    (hboundary : IsPathConnected (frontier U)) :
    ∃ δ : Path x y, range δ ⊆ (range γ \ U) ∪ frontier U := by
  have h0 : (0 : PathTime) = ⊥ := Subtype.ext rfl
  by_cases hvisit : (range γ ∩ U).Nonempty
  · obtain ⟨a, haf, ha⟩ := exists_first_closed_visit γ.toContinuousMap hU
      (by change γ ⊥ ∉ closure U; rw [← h0, Path.source]; exact hx) hvisit
    have hvisit' : (range γ.symm ∩ U).Nonempty := by simpa only [Path.symm_range] using hvisit
    obtain ⟨b, hbf, hb⟩ := exists_first_closed_visit γ.symm.toContinuousMap hU
      (by change γ.symm ⊥ ∉ closure U; rw [← h0, Path.source]; exact hy) hvisit'
    have hleft : JoinedIn ((range γ \ U) ∪ frontier U) x (γ a) :=
      (joinedIn_initial_without_open γ U a ha).mono subset_union_left
    have hright : JoinedIn ((range γ \ U) ∪ frontier U) y (γ.symm b) := by
      apply (joinedIn_initial_without_open γ.symm U b hb).mono
      rw [Path.symm_range]
      exact subset_union_left
    have hmiddle : JoinedIn ((range γ \ U) ∪ frontier U) (γ a) (γ.symm b) :=
      (hboundary.joinedIn _ haf _ hbf).mono subset_union_right
    let h := (hleft.trans hmiddle).trans hright.symm
    exact ⟨h.somePath, by rintro z ⟨t, rfl⟩; exact h.somePath_mem t⟩
  · refine ⟨γ, ?_⟩
    intro z hz
    exact Or.inl ⟨hz, fun hu => hvisit ⟨z, hz, hu⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteBoundaryDetour
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many boundary detours remove a compact set of singleton
contacts. The disks may overlap: each new boundary misses the entire
obstacle, so later detours introduce no new obstacle contacts. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem finite_boundary_detour_invariant
    {X I : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (H : Set X) (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hx : ∀ i, x ∉ closure (U i)) (hy : ∀ i, y ∉ closure (U i))
    (hb : ∀ i, IsPathConnected (frontier (U i)))
    (hmiss : ∀ i, Disjoint (frontier (U i)) H) (S : Finset I) :
    ∃ δ : Path x y,
      range δ ⊆ range γ ∪ (⋃ i ∈ S, frontier (U i)) ∧
      range δ ∩ H ⊆ (range γ ∩ H) \ (⋃ i ∈ S, U i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨γ, ?_, ?_⟩ <;> simp
  | @insert i S hi ih =>
    obtain ⟨δ, hδ, hδH⟩ := ih
    obtain ⟨ε, hε⟩ := exists_boundary_detour δ (hU i) (hx i) (hy i) (hb i)
    refine ⟨ε, ?_, ?_⟩
    · intro z hz
      rcases hε hz with hz | hz
      · rcases hδ hz.1 with hz | hz
        · exact Or.inl hz
        · right
          obtain ⟨j, hjS, hj⟩ := mem_iUnion₂.mp hz
          exact mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hjS, hj⟩
      · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hz⟩)
    · rintro z ⟨hz, hzH⟩
      rcases hε hz with hz | hz
      · obtain ⟨hzold, hzavoid⟩ := hδH ⟨hz.1, hzH⟩
        refine ⟨hzold, ?_⟩
        intro hzin
        obtain ⟨j, hjS, hj⟩ := mem_iUnion₂.mp hzin
        rcases Finset.mem_insert.mp hjS with rfl | hjS
        · exact hz.2 hj
        · exact hzavoid (mem_iUnion₂.mpr ⟨j, hjS, hj⟩)
      · exact False.elim (Set.disjoint_left.mp (hmiss i) hz hzH)

theorem exists_finite_boundary_detour
    {X I : Type*} [TopologicalSpace X] [Fintype I] {x y : X} (γ : Path x y)
    (H : Set X) (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hx : ∀ i, x ∉ closure (U i)) (hy : ∀ i, y ∉ closure (U i))
    (hb : ∀ i, IsPathConnected (frontier (U i)))
    (hmiss : ∀ i, Disjoint (frontier (U i)) H)
    (hcover : range γ ∩ H ⊆ ⋃ i, U i) :
    ∃ δ : Path x y, range δ ⊆ range γ ∪ (⋃ i, frontier (U i)) ∧
      Disjoint (range δ) H := by
  classical
  obtain ⟨δ, hδ, hδH⟩ := finite_boundary_detour_invariant γ H U hU hx hy hb hmiss Finset.univ
  refine ⟨δ, ?_, Set.disjoint_left.mpr ?_⟩
  · simpa only [Finset.mem_univ, iUnion_true] using hδ
  · intro z hz hzH
    obtain ⟨hzold, hnot⟩ := hδH ⟨hz, hzH⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hzold)
    exact hnot (mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)

theorem exists_path_avoiding_from_local_boundary_detours
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (γ : Path x y)
    {H V : Set X} (hH : IsClosed H) (hγV : range γ ⊆ V)
    (hlocal : ∀ z ∈ range γ ∩ H, ∃ U : Set X,
      IsOpen U ∧ z ∈ U ∧ closure U ⊆ V ∧ x ∉ closure U ∧ y ∉ closure U ∧
        IsPathConnected (frontier U) ∧ Disjoint (frontier U) H) :
    ∃ δ : Path x y, range δ ⊆ V ∧ Disjoint (range δ) H := by
  classical
  let K := range γ ∩ H
  have hK : IsCompact K := (isCompact_range γ.continuous).inter_right hH
  choose U hU hzU hUV hxU hyU hb hm using fun z : K => hlocal z.val z.property
  have hcover : K ⊆ ⋃ z : K, U z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzU ⟨z, hz⟩⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hU hcover
  let W : S → Set X := fun i => U i.val
  have hcov : range γ ∩ H ⊆ ⋃ i : S, W i := by
    intro z hz
    obtain ⟨i, hiS, hzi⟩ := mem_iUnion₂.mp (hS hz)
    exact mem_iUnion.mpr ⟨⟨i, hiS⟩, hzi⟩
  obtain ⟨δ, hδ, hd⟩ := exists_finite_boundary_detour γ H W
    (fun i => hU i.val) (fun i => hxU i.val) (fun i => hyU i.val)
    (fun i => hb i.val) (fun i => hm i.val) hcov
  refine ⟨δ, ?_, hd⟩
  intro z hz
  rcases hδ hz with hz | hz
  · exact hγV hz
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact hUV i.val (frontier_subset_closure hi)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BandMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Haar measure of a projected band

The projection of a real interval of length `b - a` is contained in
the circle ball with midpoint `(a + b) / 2` and radius `(b - a) / 2`.
This gives the manuscript's band-incidence bound, including long bands.
-/

open Set MeasureTheory Metric
open scoped Topology

namespace CircleDomainRigidity

/-- The band-incidence estimate in the coordinates used by the paper:
the budget bounds the difference of the actual upper and lower limits. -/
theorem volume_circleBandGraph_incidence_le_budget
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X]
    {G : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ y ∈ G, |f y| ≤ M)
    {x : X} (hx : x ∈ closure G) {a : ℝ}
    (hbudget : Filter.limsup f (𝓝[G] x) - Filter.liminf f (𝓝[G] x) ≤ a) :
    volume {t : AddCircle (1 : ℝ) | (x, t) ∈ circleBandGraph G f} ≤
      ENNReal.ofReal a := by
  rw [circleBandGraph_fiber_eq_image_realFiber,
    intervalFiberHull_clusterGraph_eq_boundary_band hM hx]
  exact (volume_addCircle_image_Icc_le _ _).trans
    (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hbudget))

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Topology_ClopenNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a component by a clopen neighborhood

This is the compact-space step before the smooth contour construction:
a neighborhood containing a whole component contains a clopen
neighborhood of that component's base point. Applied in a closed
obstacle set, it isolates a singleton dust component.
-/

open Set

namespace CircleDomainRigidity

theorem exists_clopen_between_component_and_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) {O : Set X} (hO : IsOpen O) (hC : connectedComponent x ⊆ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  classical
  have hd : Disjoint Oᶜ (connectedComponent x) :=
    Set.disjoint_left.mpr (fun y hy hyC => hy (hC hyC))
  rw [connectedComponent_eq_iInter_isClopen x] at hd
  obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun V : {V : Set X // IsClopen V ∧ x ∈ V} => V.val)
    (fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  refine ⟨⋂ V ∈ s, (V : Set X), isClopen_biInter_finset (fun V _ => V.property.1),
    mem_iInter₂.mpr (fun V _ => V.property.2), ?_⟩
  intro y hy
  by_contra hyO
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy

/-- In particular, singleton components in a compact closed obstacle
have arbitrarily small relatively clopen neighborhoods. -/
theorem exists_clopen_neighborhood_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (hC : connectedComponent x = {x}) {O : Set X}
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O :=
  exists_clopen_between_component_and_open x hO (by simpa only [hC, singleton_subset_iff] using hx)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ComponentLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localizing nondegenerate components

Boundary bumping turns a nondegenerate continuum through a point into
one in any prescribed neighborhood. This is the localization used in
the lower-grid obstacle argument. Totally disconnected dust cannot
destroy a singleton component of a compact closed obstacle.
-/

open Set Topology

namespace CircleDomainRigidity

theorem exists_nontrivial_subcontinuum_in_open
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C U : Set X} (hcompact : IsCompact C) (hconn : IsConnected C)
    (hnt : C.Nontrivial) {x : X} (hx : x ∈ C) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D.Nontrivial ∧ x ∈ D ∧ D ⊆ C ∩ U := by
  classical
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  let xc : C := ⟨x, hx⟩
  let yc : C := ⟨y, hy⟩
  let O : Set C := (Subtype.val ⁻¹' U) ∩ {yc}ᶜ
  have hO : IsOpen O := (hU.preimage continuous_subtype_val).inter
    isClosed_singleton.isOpen_compl
  have hxO : xc ∈ O := ⟨hxU, fun heq => hyx (congrArg Subtype.val heq).symm⟩
  obtain ⟨N, hNnhds, hNclosed, hNO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hxO)
  have hxN : xc ∈ N := mem_of_mem_nhds hNnhds
  have hNproper : N ≠ univ := by
    intro heq
    have hyN : yc ∈ N := by rw [heq]; trivial
    exact (hNO hyN).2 rfl
  obtain ⟨z, hz, hzfront⟩ := component_meets_frontier hNclosed hNproper hxN
  let K := connectedComponentIn N xc
  have hKclosed : IsClosed K := by
    change IsClosed (connectedComponentIn N xc)
    rw [connectedComponentIn_eq_image hxN]
    exact hNclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hxN
  let D : Set X := Subtype.val '' K
  have hxD : x ∈ D := ⟨xc, mem_connectedComponentIn hxN, rfl⟩
  have hzD : z.val ∈ D := ⟨z, hz, rfl⟩
  have hzx : z.val ≠ x := by
    intro heq
    have hzc : z = xc := Subtype.ext heq
    have hxfront : xc ∈ frontier N := hzc ▸ hzfront
    exact hxfront.2 (mem_interior_iff_mem_nhds.mpr hNnhds)
  refine ⟨D, hKclosed.isCompact.image continuous_subtype_val,
    hKconn.image _ continuous_subtype_val.continuousOn,
    ⟨x, hxD, z.val, hzD, hzx.symm⟩, hxD, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.property, (hNO (connectedComponentIn_subset N xc hw)).1⟩

/-- To rule out a nondegenerate component, it suffices to rule out small
subcontinua through the point in one open neighborhood. -/
theorem component_eq_singleton_of_local_no_continuum
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F U : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hU : IsOpen U) (hxU : x ∈ U)
    (hno : ∀ D : Set X, IsCompact D → IsConnected D → x ∈ D →
      D ⊆ F ∩ U → ¬ D.Nontrivial) :
    connectedComponentIn F x = {x} := by
  have hclosed : IsClosed (connectedComponentIn F x) := by
    rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn := isConnected_connectedComponentIn_iff.mpr hx
  have hsub : (connectedComponentIn F x).Subsingleton := by
    by_contra hn
    have hnt : (connectedComponentIn F x).Nontrivial := Set.not_subsingleton_iff.mp hn
    obtain ⟨D, hDcompact, hDconn, hDnt, hxD, hDsub⟩ :=
      exists_nontrivial_subcontinuum_in_open hclosed.isCompact hconn hnt
        (mem_connectedComponentIn hx) hU hxU
    exact hno D hDcompact hDconn hxD
      (fun y hy => ⟨connectedComponentIn_subset F x (hDsub hy).1, (hDsub hy).2⟩) hDnt
  exact hsub.eq_singleton_of_mem (mem_connectedComponentIn hx)

/-- Adding compact totally disconnected dust preserves every singleton
component of a closed obstacle and gives singleton components off it. -/
theorem component_union_dust_eq_singleton
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F B : Set X} (hF : IsClosed F) (hB : IsClosed B)
    (htd : IsTotallyDisconnected B) {x : X} (hx : x ∈ F ∪ B)
    (hsing : x ∈ F → connectedComponentIn F x = {x}) :
    connectedComponentIn (F ∪ B) x = {x} := by
  let C := connectedComponentIn (F ∪ B) x
  have hclosed : IsClosed C := by
    change IsClosed (connectedComponentIn (F ∪ B) x)
    rw [connectedComponentIn_eq_image hx]
    exact (hF.union hB).isClosedMap_subtype_val _ isClosed_connectedComponent
  have hconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hsub : C.Subsingleton := by
    by_contra hn
    have hnt : C.Nontrivial := Set.not_subsingleton_iff.mp hn
    have hCF : C ⊆ F := continuum_subset_closed_of_totallyDisconnected
      hclosed.isCompact hconn hnt hF htd (connectedComponentIn_subset (F ∪ B) x)
    have hCsing : C ⊆ {x} := by
      rw [← hsing (hCF hxC)]
      exact hconn.isPreconnected.subset_connectedComponentIn hxC hCF
    exact hn (fun _ ha _ hb => (mem_singleton_iff.mp (hCsing ha)).trans
      (mem_singleton_iff.mp (hCsing hb)).symm)
  exact hsub.eq_singleton_of_mem hxC

/-- Near a point, a finite closed level union only uses the levels which
contain that point. A singleton component in this smaller union is
therefore a singleton component in the entire union. -/
theorem component_finite_union_eq_singleton
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (s : Finset ι) (H : ι → Set X) (hH : ∀ i ∈ s, IsClosed (H i))
    {x : X} (hx : x ∈ ⋃ i ∈ s, H i)
    (hpresent : connectedComponentIn (⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i) x = {x}) :
    connectedComponentIn (⋃ i ∈ s, H i) x = {x} := by
  classical
  let F := ⋃ i ∈ s, H i
  let B := ⋃ i ∈ s.filter (fun i => x ∉ H i), H i
  have hF : IsClosed F := isClosed_biUnion_finset (fun i hi => hH i hi)
  have hB : IsClosed B := isClosed_biUnion_finset (fun i hi => hH i (Finset.mem_filter.mp hi).1)
  have hxB : x ∉ B := by
    simp only [B, mem_iUnion, exists_prop, Finset.mem_filter]
    rintro ⟨i, ⟨_, hxi⟩, hxi'⟩
    exact hxi hxi'
  apply component_eq_singleton_of_local_no_continuum hF hx hB.isOpen_compl hxB
  intro D hDcompact hDconn hxD hDsub hDnt
  have hsub : D ⊆ ⋃ i ∈ s, ⋃ (_ : x ∈ H i), H i := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hDsub hy).1
    have hxi : x ∈ H i := by
      by_contra hn
      exact (hDsub hy).2 (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩, hyi⟩)
    exact mem_iUnion₂.mpr ⟨i, hi, mem_iUnion.mpr ⟨hxi, hyi⟩⟩
  have hsingle : D ⊆ {x} := by
    rw [← hpresent]
    exact hDconn.isPreconnected.subset_connectedComponentIn hxD hsub
  exact hDnt.not_subsingleton (fun _ ha _ hb => (mem_singleton_iff.mp (hsingle ha)).trans
    (mem_singleton_iff.mp (hsingle hb)).symm)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

/-- Finite smooth disk cover of the physical fiber at a singleton quotient
component. The connected unbounded complement condition is imposed on the
specified physical preimage, exactly where the filling argument uses it. -/
theorem exists_small_physical_disks_at_singleton_component
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (π : Sphere → X) (hπ : Continuous π) {F V : Set X}
    (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hinfty : π OnePoint.infty ∉ V)
    (hVconn : IsPreconnected ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    (hVunbounded : ¬ Bornology.IsBounded ((fun z : ℂ => π (z : Sphere)) ⁻¹' V)ᶜ)
    {G : Set Sphere} (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      s.Finite ∧
      (∀ z : ℂ, π (z : Sphere) = x → z ∈ ⋃ i ∈ s, jordanInterior (H i)) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧
        Topology.IsEmbedding (γ i) ∧ frontier (jordanInterior (H i)) = range (γ i) ∧
        (∀ z ∈ frontier (jordanInterior (H i)), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) := by
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (hAV h)
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hs, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_smooth_jordan_cover hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV) hVconn hVunbounded
  refine ⟨f, t, γ, H, s, hs, ?_, hd, hinside, ?_⟩
  · intro z hz
    apply hcov
    change π (z : Sphere) ∈ A
    simpa only [hz] using hxA
  · intro i hi
    obtain ⟨hγsmooth, hγemb, hγfront, havoid⟩ := hcurves i hi
    refine ⟨hγsmooth, hγemb, hγfront, ?_⟩
    intro z hz
    have hnotF : π (z : Sphere) ∉ F := fun h => Set.disjoint_left.mp havoid hz h
    refine ⟨?_, hnotF⟩
    by_contra h
    exact hnotF (hbad _ h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallQuotientDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth physical disks from the component quotient

These statements combine compact clopen isolation, actual contour selection,
the component quotient, and the infinity-chart argument. Connectedness and
unboundedness of the physical exterior are conclusions of the preceding
lemmas, not additional disk-selection hypotheses.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The small physical disk construction for a singleton component of
the actual quotient obstacle. -/
theorem smoothPhysicalDiskCover_of_component_quotient
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    SmoothPhysicalDiskCover π x V F G := by
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  exact exists_small_physical_disks_at_singleton_component hsard hschoenflies
    π hπ hF hx hcomponent hV hxV (fun h => hinfty (subset_closure h))
      hphysical hunbounded hbad

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SinglePhysicalDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single smooth physical disk about a quotient singleton

Connectedness of the fiber upgrades the finite disjoint cover to a single
disk. The general open-family lemma does not need finiteness.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_member_containing_connected_set
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let V : Set X := ⋃ j ∈ ({i}ᶜ : Set I), U j
  have hV : IsOpen V := isOpen_biUnion (fun j _ => hU j)
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp (hd (fun h => hj (mem_singleton_iff.mpr h.symm))) hz hzj
  have hSC : S ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, by simpa using hji, hzj⟩)
  rcases hS.isPreconnected.subset_or_subset (hU i) hV hUV hSC with h | h
  · exact ⟨i, h⟩
  · exact (Set.disjoint_left.mp hUV hxi (h hx)).elim

theorem isConnected_finite_fiber
    {X : Type*} (π : Sphere → X) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {x : X} (hne : π OnePoint.infty ≠ x) :
    IsConnected {z : ℂ | π (z : Sphere) = x} := by
  have heq : ((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x} = π ⁻¹' {x} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hne]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  have hconn : IsConnected (((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x}) :=
    heq.symm ▸ hfibers x
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hconn.isPreconnected⟩
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨z, hz, _⟩ := hp
  exact ⟨z, hz⟩

/-- A finite disjoint disk cover of a connected physical fiber contains
one disk covering that entire fiber. -/
theorem SmoothPhysicalDiskCover.exists_single_disk
    {X : Type*} {π : Sphere → X} {x : X} {V F : Set X} {G : Set Sphere}
    (hcover : SmoothPhysicalDiskCover π x V F G)
    (hfiber : IsConnected {z : ℂ | π (z : Sphere) = x}) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F := by
  classical
  obtain ⟨f, t, γ, H, s, _, hcov, hd, hinside, hcurves⟩ := hcover
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcov' : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov z hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcov'
  exact ⟨H i, γ i, hi, hinside i i.property, hcurves i i.property⟩

/-- Exact single-disk form of the small physical neighborhood statement
for the actual component quotient. -/
theorem exists_single_small_physical_disk
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F := by
  have hcover := smoothPhysicalDiskCover_of_component_quotient hsard hschoenflies
    G π hπ hclosed hsurj hr hF hx hcomponent hV hxV hVconn hinfty hbad
  apply hcover.exists_single_disk
  apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
  intro heq
  exact hinfty (subset_closure (heq.symm ▸ hxV))

end CircleDomainRigidity

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
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedFrontier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A saturated open set with closed projected closure has its exact projected
frontier. This identifies the boundary of the quotient collars. -/

open Set Function

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem frontier_image_of_saturated_open (π : X → Y) (hπ : Continuous π)
    (U : Set X) (hU : IsOpen U) (ho : IsOpen (π '' U))
    (hc : IsClosed (π '' closure U)) (hsat : π ⁻¹' (π '' U) = U) :
    frontier (π '' U) = π '' frontier U := by
  have hcl : closure (π '' U) = π '' closure U := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hc
    · exact image_closure_subset_closure_image hπ
  rw [ho.frontier_eq, hcl, hU.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, fun h => hy ⟨x, h, rfl⟩⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hxn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro h
    exact hxn (hsat ▸ h)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientDiskTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Topology of projected physical disks

Physical Jordan disks with boundary in the original domain have saturated
interiors and saturated closures. Their images are open with connected
complements, and disjoint physical closed disks give disjoint quotient closed
disks. These properties allow finite dust covers to be used in the descending
grid construction without postulating a disk-selection lemma.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem closure_image_jordanInterior
    {Y : Type*} [TopologicalSpace Y] (π : Sphere → Y)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (H : ℂ ≃ₜ ℂ) :
    closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior H)) := by
  rw [hclosed.closure_image_eq_of_continuous hπ, closure_sphere_image_jordanInterior]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SingletonDetourNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing small physical disk construction supplies actual
quotient neighborhoods with path connected boundaries avoiding the
whole obstacle. These are the neighborhoods used in finite detours. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_singleton_detour_neighborhood
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hsing : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ closure U ⊆ V ∧
      IsPathConnected (frontier U) ∧ Disjoint (frontier U) F := by
  obtain ⟨J, c, hcover, hJV, hc, _, hfront, hboundary⟩ :=
    exists_single_small_physical_disk hsard hsch G π hπ hclosed hsurj hr
      hF hx hsing hV hxV hVconn hinfty hbad
  let W : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior J
  let U : Set X := π '' W
  have hW : IsOpen W := OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)
  have hU : IsOpen U := isOpen_image_jordanInterior_of_component_collapse
    G π hπ hclosed hsurj hr J (fun z hz => (hboundary z hz).1)
  have hcl : closure U = π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior J)) :=
    closure_image_jordanInterior π hπ hclosed J
  have hsat : π ⁻¹' U = W := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr J (fun z hz => (hboundary z hz).1)
  have hcW : IsCompact (closure W) := by
    rw [closure_sphere_image_jordanInterior]
    exact (isCompact_closure_jordanInterior J).image OnePoint.continuous_coe
  have hUF : frontier U = π '' (((↑) : ℂ → Sphere) '' range c) := by
    rw [frontier_image_of_saturated_open π hπ W hW hU
      (hcW.image hπ).isClosed hsat,
      frontier_sphere_image_jordanInterior, hfront]
  refine ⟨U, hU, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hsurj x
    cases p using OnePoint.rec with
    | infty => exact False.elim (hinfty (hp.symm ▸ subset_closure hxV))
    | coe z => exact ⟨z, ⟨z, hcover hp, rfl⟩, hp⟩
  · rw [hcl]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hJV hz
  · rw [hUF]
    exact ((isPathConnected_range hc.continuous).image OnePoint.continuous_coe).image hπ
  · rw [hUF]
    apply Set.disjoint_left.mpr
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hmem
    exact (hboundary z (hfront.symm ▸ hz)).2 hmem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SingletonPathDetour
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A path whose contacts with a closed level all belong to singleton
components can be deformed off that level, inside its prescribed open
mask. The small neighborhoods come from the actual component quotient. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_path_avoiding_singleton_level
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V)
    (hsing : ∀ z ∈ range γ ∩ H, connectedComponentIn H z = {z}) :
    ∃ δ : Path x y, range δ ⊆ V ∧ Disjoint (range δ) H := by
  apply exists_path_avoiding_from_local_boundary_detours γ hH hγV
  intro z hz
  let W : Set Sphere := V ∩ ({x, y} : Set Sphere)ᶜ
  have hxy : IsClosed ({x, y} : Set Sphere) := by
    simpa only [singleton_union] using
      (isClosed_singleton.union isClosed_singleton : IsClosed ({x} ∪ {y} : Set Sphere))
  have hW : IsOpen W := hV.inter hxy.isOpen_compl
  have hzW : z ∈ W := by
    refine ⟨hγV hz.1, ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun he => hx (he ▸ hz.2), fun he => hy (he ▸ hz.2)⟩
  obtain ⟨N, hN, hzN, hNW, hNc⟩ := exists_sphere_neighborhood_connected_compl hW hzW
  have hNinf : π OnePoint.infty ∉ closure N := fun hn => hinfty (hNW hn).1
  have hs : connectedComponentIn (H ∪ B) z = {z} :=
    component_union_dust_eq_singleton hH hB hTD (Or.inl hz.2) (fun _ => hsing z hz)
  obtain ⟨U, hU, hzU, hUN, hbU, hmU⟩ := exists_singleton_detour_neighborhood
    hsard hsch G π hπ hclosed hsurj hr (hH.union hB) (Or.inl hz.2)
    hs hN hzN hNc hNinf (fun p hp => Or.inr (hbad p hp))
  have hUW : closure U ⊆ W := hUN.trans (subset_closure.trans hNW)
  refine ⟨U, hU, hzU, fun a ha => (hUW ha).1, ?_, ?_, hbU,
    hmU.mono_right subset_union_left⟩
  · intro hxU
    exact (hUW hxU).2 (by simp)
  · intro hyU
    exact (hUW hyU).2 (by simp)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SingletonBandCrossing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The topological threshold step in Lemma 6.6. A path joining opposite
band values must have a nonsingleton level contact. Consequently, when
free contacts have singleton components, a threshold is paid at a domain
point or a flagged point. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_nonsingleton_band_contact
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {K : Set (Sphere × ℝ)} (hK : IsCompact K)
    (hne : ∀ z ∈ V, {t : ℝ | (z, t) ∈ K}.Nonempty)
    (hinterval : ∀ z ∈ V, OrdConnected {t : ℝ | (z, t) ∈ K})
    {v : ℝ} (hlevel : ∀ z ∈ V, (z, v) ∈ K → z ∈ H)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V) {a b : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b) :
    ∃ z ∈ range γ ∩ H, (connectedComponentIn H z).Nontrivial := by
  by_contra! hn
  have hs : ∀ z ∈ range γ ∩ H, connectedComponentIn H z = {z} := by
    intro z hz
    exact (hn z hz).eq_singleton_of_mem
      (mem_connectedComponentIn hz.2)
  obtain ⟨δ, hδV, hδH⟩ := exists_path_avoiding_singleton_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hH hV hinfty hx hy γ hγV hs
  obtain ⟨z, hz, hzv⟩ := compact_band_crossing hK
    (isConnected_range δ.continuous).isPreconnected
    (fun z hz => hne z (hδV hz)) (fun z hz => hinterval z (hδV hz))
    ⟨0, δ.source⟩ ⟨1, δ.target⟩ ha hb hav hvb
  exact Set.disjoint_left.mp hδH hz (hlevel z (hδV hz) hzv)

theorem singleton_free_contacts_force_paid_level
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B H V Free Paid : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hH : IsClosed H) (hV : IsOpen V)
    (hinfty : π OnePoint.infty ∉ V)
    {K : Set (Sphere × ℝ)} (hK : IsCompact K)
    (hne : ∀ z ∈ V, {t : ℝ | (z, t) ∈ K}.Nonempty)
    (hinterval : ∀ z ∈ V, OrdConnected {t : ℝ | (z, t) ∈ K})
    {v : ℝ} (hlevel : ∀ z ∈ V, (z, v) ∈ K → z ∈ H)
    {x y : Sphere} (hx : x ∉ H) (hy : y ∉ H) (γ : Path x y)
    (hγV : range γ ⊆ V) {a b : ℝ}
    (ha : (x, a) ∈ K) (hb : (y, b) ∈ K) (hav : a ≤ v) (hvb : v ≤ b)
    (hcover : range γ ∩ H ⊆ Free ∪ Paid)
    (hfree : ∀ z ∈ range γ ∩ H, z ∈ Free →
      ¬ (connectedComponentIn H z).Nontrivial) :
    (range γ ∩ H ∩ Paid).Nonempty := by
  obtain ⟨z, hz, hnt⟩ := exists_nonsingleton_band_contact hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hH hV hinfty hK hne hinterval
    hlevel hx hy γ hγV ha hb hav hvb
  rcases hcover hz with hf | hp
  · exact (hfree z hz hf hnt).elim
  · exact ⟨z, hz, hp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealBandPaidThreshold
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual real-coordinate band levels satisfy the paid-threshold
conclusion used in the local variation argument. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_band_paid_threshold
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hab : b - a < 1) (hav : a < v) (hvb : v < b)
    (hfree : ∀ z ∈ range γ ∩ {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f},
      z ∈ B \ Flags →
      ¬ (connectedComponentIn {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f} z).Nontrivial) :
    ∃ z ∈ range γ, (z ∈ D ∨ z ∈ Flags) ∧
      (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f := by
  let H := {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f}
  have hva : (v : AddCircle (1 : ℝ)) ≠ (a : AddCircle (1 : ℝ)) := by
    intro he
    have hvi : v ∈ Ico a (a + 1) := ⟨hav.le, by linarith⟩
    have hai : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
    exact hav.ne' ((AddCircle.coe_eq_coe_iff_of_mem_Ico hvi hai).mp he)
  have hvb' : (v : AddCircle (1 : ℝ)) ≠ (b : AddCircle (1 : ℝ)) := by
    intro he
    have hvi : v ∈ Ico a (a + 1) := ⟨hav.le, by linarith⟩
    have hbi : b ∈ Ico a (a + 1) := ⟨by linarith, by linarith⟩
    exact hvb.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico hvi hbi).mp he)
  have hxH : x ∉ H := by
    rintro ⟨⟨z, t⟩, ht, he⟩
    change (z, (t : AddCircle (1 : ℝ))) = (x, (v : AddCircle (1 : ℝ))) at he
    have hz : z = x := congrArg Prod.fst he
    have htEq : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
    subst z
    exact hva (htEq.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) ((ha t).mp ht)))
  have hyH : y ∉ H := by
    rintro ⟨⟨z, t⟩, ht, he⟩
    change (z, (t : AddCircle (1 : ℝ))) = (y, (v : AddCircle (1 : ℝ))) at he
    have hz : z = y := congrArg Prod.fst he
    have htEq : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
    subst z
    exact hvb' (htEq.symm.trans (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) ((hb t).mp ht)))
  have hcl (z : Sphere) : z ∈ closure D := by rw [hdense.closure_eq]; trivial
  obtain ⟨z, hz, hp⟩ := singleton_free_contacts_force_paid_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad
    (isCompact_circleBandLevel hM (v : AddCircle (1 : ℝ))).isClosed hV hinfty
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM))
    (fun z _ => by
      obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z)
      exact ⟨t, subset_intervalFiberHull _ ht⟩)
    (fun z _ => by
      rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) z
        (clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z))]
      exact ordConnected_Icc)
    (fun z _ hz => ⟨(z, v), hz, rfl⟩)
    hxH hyH γ hγV ((ha a).mpr rfl) ((hb b).mpr rfl) hav.le hvb.le
    (Free := B \ Flags) (Paid := D ∪ Flags)
    (by
      intro z _
      by_cases hzB : z ∈ B
      · by_cases hzF : z ∈ Flags
        · exact Or.inr (Or.inr hzF)
        · exact Or.inl ⟨hzB, hzF⟩
      · exact Or.inr (Or.inl (hBD hzB))) hfree
  exact ⟨z, hz.1, hp, hz.2⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealBandPaidValues
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a common branch range shorter than one, the paid circle threshold
is exactly the real threshold. Domain hits contribute a coordinate value;
flagged hits contribute a member of the actual real band. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem real_band_paid_values
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hav : a < v) (hvb : v < b) (hv : v ∈ Ico c (c + 1))
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ z ∈ range γ ∩ {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f},
      z ∈ B \ Flags →
      ¬ (connectedComponentIn {z | (z, (v : AddCircle (1 : ℝ))) ∈ circleBandGraph D f} z).Nontrivial) :
    v ∈ f '' (range γ ∩ D) ∨
      ∃ z ∈ range γ ∩ Flags, (z, v) ∈ intervalFiberHull (clusterGraph D f) := by
  have haV : x ∈ V := hγV ⟨0, γ.source⟩
  have hbV : y ∈ V := hγV ⟨1, γ.target⟩
  have hai := hbranch x haV a ((ha a).mpr rfl)
  have hbi := hbranch y hbV b ((hb b).mpr rfl)
  have hab : b - a < 1 := by linarith [hai.1, hbi.2]
  obtain ⟨z, hz, hp, hc⟩ := real_band_paid_threshold hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hBD hdense hV hinfty hM γ hγV
    ha hb hab hav hvb hfree
  obtain ⟨⟨w, t⟩, ht, he⟩ := hc
  change (w, (t : AddCircle (1 : ℝ))) = (z, (v : AddCircle (1 : ℝ))) at he
  have hw : w = z := congrArg Prod.fst he
  have htv : (t : AddCircle (1 : ℝ)) = (v : AddCircle (1 : ℝ)) := congrArg Prod.snd he
  subst w
  have htEq : t = v := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hbranch z (hγV hz) t ht) hv).mp htv
  subst t
  rcases hp with hzD | hzF
  · exact Or.inl ⟨z, ⟨hz, hzD⟩,
      ((intervalFiberHull_clusterGraph_on_open hD hf hzD).mp ht).symm⟩
  · exact Or.inr ⟨z, ⟨hz, hzF⟩, ht⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBandPathPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the actual paid-threshold conclusion yields the local
variation estimate in image-measure form. Only the generic singleton
statement from the independent-level argument is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem real_band_path_image_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal (b - a) ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  let : Countable ↥(range γ ∩ Flags) := (hFlags.mono inter_subset_right).to_subtype
  by_cases hab : a < b
  · have hai := hbranch x (hγV ⟨0, γ.source⟩) a ((ha a).mpr rfl)
    have hbi := hbranch y (hγV ⟨1, γ.target⟩) b ((hb b).mpr rfl)
    have hsub : Ioo a b ⊆ Ioc c (c + 1) := by
      intro t ht
      exact ⟨hai.1.trans_lt ht.1, (ht.2.trans hbi.2).le⟩
    have hreal := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_real_interval_of_ae_circle _ hfree c)
    have hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
        t ∈ f '' (range γ ∩ D) ∨ ∃ z : ↥(range γ ∩ Flags),
          (z.val, t) ∈ intervalFiberHull (clusterGraph D f) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hreal] with t ht hgood
      have hti : t ∈ Ico c (c + 1) := ⟨hai.1.trans ht.1.le, ht.2.trans hbi.2⟩
      rcases real_band_paid_values hsard hsch G π hπ hclosed hsurj hr
        hB hTD hbad hBD hdense hD hV hinfty hM hf γ hγV ha hb ht.1 ht.2 hti
        hbranch hgood with hdom | ⟨z, hz, hzt⟩
      · exact Or.inl hdom
      · exact Or.inr ⟨⟨z, hz⟩, hzt⟩
    exact interval_band_payment_of_ae_cover hM (fun z : ↥(range γ ∩ Flags) => z.val)
      (fun z => by rw [hdense.closure_eq]; trivial) (f '' (range γ ∩ D)) a b hcover
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hab))]
    exact bot_le

theorem real_band_path_abs_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact real_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf γ hγV ha hb hbranch hfree
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    rw [abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    have hγ' : range γ.symm ⊆ V := by simpa only [Path.symm_range] using hγV
    have hf' : ∀ᵐ θ : UnitAddCircle ∂volume,
        ∀ z ∈ range γ.symm ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
          ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial := by
      simpa only [Path.symm_range] using hfree
    have hp := real_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf γ.symm hγ' hb ha hbranch hf'
    have hset : range γ.symm ∩ Flags = range γ ∩ Flags := by rw [Path.symm_range]
    rw [hset] at hp
    simpa only [Path.symm_range] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IntervalPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

noncomputable section
namespace CircleDomainRigidity

theorem intervalPath_range {X : Type*} [MetricSpace X] (γ : C(PathTime, X))
    {a b : PathTime} (hab : a < b) :
    range (intervalPath γ a b) = γ '' Icc a b := by
  change range (γ ∘ affinePathTime a b) = _
  rw [range_comp, range_affinePathTime hab]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBandIntervalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute variation on an actual parameter interval, paid by domain
image length and the atomic measure of flagged visits. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem real_band_interval_image_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    (γ : C(PathTime, Sphere)) {r s : PathTime} (hrs : r < s)
    (hγV : γ '' Icc r s ⊆ V)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ '' Icc r s ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (γ '' Icc r s ∩ D)) + boundaryTimeMeasure γ m (Icc r s) := by
  let α := intervalPath γ r s
  have hrange : range α = γ '' Icc r s := intervalPath_range γ hrs
  have hp := real_band_path_abs_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf α
    (by simpa only [hrange] using hγV) ha hb hbranch
    (by simpa only [hrange] using hfree)
  have hset : range α ∩ Flags = γ '' Icc r s ∩ Flags := by rw [hrange]
  rw [hset, hrange] at hp
  apply hp.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' z : ↥(γ '' Icc r s ∩ Flags), m z.val :=
      ENNReal.tsum_le_tsum (fun z => hm z.val z.property.2)
    _ ≤ _ := boundaryTimeMeasure_image_le γ m measurableSet_Icc inter_subset_left

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathImageCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CurveCoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plane-to-line specialization of Esmayli–Hajłasz, *The Coarea
Inequality*, Ann. Fenn. Math. 46 (2021), 965–991, Theorem 1.1,
DOI 10.5186/aasfm.2021.4654. The authors' manuscript is
https://arxiv.org/pdf/2006.00419 (Theorem 1.1, p. 1; proof, §7).

Only s=t=1, X=ℂ and Y=ℝ is retained. The Hausdorff normalization
constant is one in these dimensions. The source's measurability clause
requires finite H¹ measure and a measurable set in a boundedly compact
space; all these hypotheses are retained. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

 theorem cardinalitySum_le_hausdorffZero (A : Set ℂ) :
    (∑' z : ℂ, if z ∈ A then (1 : ℝ≥0∞) else 0) ≤ (μH[0] : Measure ℂ) A := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let E := F.filter (fun z => z ∈ A)
  calc
    (∑ z ∈ F, if z ∈ A then (1 : ℝ≥0∞) else 0) =
        ∑ z ∈ E, (μH[0] : Measure ℂ) {z} := by
      simp only [E, Finset.sum_filter, Measure.hausdorffMeasure_zero_singleton]
    _ = (μH[0] : Measure ℂ) E := sum_measure_singleton
    _ ≤ (μH[0] : Measure ℂ) A := measure_mono (fun z hz => (Finset.mem_filter.mp hz).2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactPhysicalFiberCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarea for the actual distinct intersections of quotient arcs with
compact physical slices. Length is measured before the coordinate change. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)] in
 theorem pathImageCount_image_le_hausdorffZero (π : ℂ → X) (A : Set ℂ)
    (γ : C(PathTime, X)) :
    pathImageCount (π '' A) γ ≤ (μH[0] : Measure ℂ) (A ∩ π ⁻¹' range γ) := by
  rw [pathImageCount_eq_iSup]
  apply iSup_le
  intro n
  split
  · rename_i hn
    obtain ⟨t, ht, hA⟩ := hn
    choose z hz he using hA
    have hzinj : Injective z := by
      intro i j hij
      apply ht
      change γ (t i) = γ (t j)
      rw [← he i, ← he j, hij]
    have hmem (i : Fin n) : z i ∈ A ∩ π ⁻¹' range γ :=
      ⟨hz i, ⟨t i, (he i).symm⟩⟩
    calc
      (n : ℝ≥0∞) = ∑' i : Fin n,
          if z i ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 := by simp [hmem]
      _ ≤ ∑' w : ℂ, if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0 :=
        by
          simpa [mem_inter_iff] using ENNReal.tsum_comp_le_tsum_of_injective hzinj
            (fun w : ℂ => if w ∈ A ∩ π ⁻¹' range γ then (1 : ℝ≥0∞) else 0)
      _ ≤ _ := by
        simpa [mem_inter_iff] using
          cardinalitySum_le_hausdorffZero (A ∩ π ⁻¹' range γ)
  · exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalSliceOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical occupation measure controls compact physical slices. A local inverse chart bound suffices; no regularity
of the Jordan coordinate change is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [MeasurableSpace Y] [BorelSpace Y] in
 theorem physical_chart_image_subset (e : G ≃ₜ U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G) (γ : C(PathTime, X)) :
    φ '' (A ∩ (π ∘ φ) ⁻¹' range γ) ⊆
      (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht⟩ := hz.2
  have hez := he ⟨φ z, hA hz.1⟩
  have htu : γ t ∈ U := by
    rw [ht]
    change π (φ z) ∈ U
    rw [← hez]
    exact (e ⟨φ z, hA hz.1⟩).property
  refine ⟨t, htu, ?_⟩
  change physicalValue e y₀ (γ t) = φ z
  rw [physicalValue, dite_eq_left htu]
  have heq : (⟨γ t, htu⟩ : U) = e ⟨φ z, hA hz.1⟩ :=
    Subtype.ext (ht.trans hez.symm)
  rw [heq, e.symm_apply_apply]

 theorem compact_chart_length_le_occupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) ≤
      (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
  let E := A ∩ (π ∘ φ) ⁻¹' range γ.val
  have hEA : E ⊆ A := inter_subset_left
  have hid : j '' (φ '' E) = E := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hj z (hEA hz)]
    · intro hw
      exact ⟨φ w, ⟨w, hw, rfl⟩, hj w (hEA hw)⟩
  calc
    (μH[1] : Measure ℂ) E = (μH[1] : Measure ℂ) (j '' (φ '' E)) := congrArg _ hid.symm
    _ ≤ (B : ℝ≥0∞) * (μH[1] : Measure Y) (φ '' E) := by
      simpa only [ENNReal.rpow_one] using
        (hB.mono (image_mono hEA)).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ (B : ℝ≥0∞) * physicalOccupationCode e y₀ γ.val (φ '' A) := by
      apply mul_le_mul' le_rfl
      rw [physicalOccupationCode_eq e y₀ γ]
      have hsub := physical_chart_image_subset e y₀ π he φ hA γ.val
      calc
        (μH[1] : Measure Y) (φ '' E) ≤ (μH[1] : Measure Y)
            ((φ '' A) ∩ ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) :=
          measure_mono (subset_inter (image_mono hEA) hsub)
        _ = ((μH[1] : Measure Y).restrict
            ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) (φ '' A) :=
          (Measure.restrict_apply hφA).symm
        _ ≤ _ := physical_image_hausdorff_le_occupation e hU y₀ γ _

end CircleDomainRigidity

end

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCurveCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differential-weighted curve coarea, derived from the published
constant-Lipschitz inequality by a disjoint local cover. No new coarea
input is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem curve_coarea_lipschitzOn
    (hcoarea : PlanarLipschitzFiberCoarea) {A : Set ℂ} (hA : MeasurableSet A)
    (hfin : (μH[1] : Measure ℂ) A < ∞) {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f A) :
    AEMeasurable (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) volume ∧
      (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure ℂ) A := by
  obtain ⟨g, hg, he⟩ := hf.extend_real
  have hsets (t : ℝ) : A ∩ f ⁻¹' {t} = A ∩ g ⁻¹' {t} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact and_congr_right (fun hz => by rw [he hz])
  simpa only [hsets] using hcoarea A hA hfin L g hg

theorem smooth_curve_coarea_add_error
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ + ENNReal.ofReal ε
        ∂(μH[1] : Measure ℂ) := by
  obtain ⟨U, L, hU, hcover, _, hLip, hbound⟩ := exists_countable_derivative_cover hD hf hε
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hEA (n : ℕ) : E n ⊆ A := inter_subset_left
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  have hpieces (n : ℕ) := curve_coarea_lipschitzOn hcoarea (hE n)
    ((measure_mono (hEA n)).trans_lt hfin) ((hLip n).mono (hEU n))
  have hcount (t : ℝ) : (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t}) ≤
      ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) := by
    rw [← hEq, iUnion_inter]
    exact measure_iUnion_le _
  calc
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
        ∫⁻ t, ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) := lintegral_mono hcount
    _ = ∑' n, ∫⁻ t, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t}) :=
      lintegral_tsum (fun n => (hpieces n).1)
    _ ≤ ∑' n, (L n : ℝ≥0∞) * (μH[1] : Measure ℂ) (E n) :=
      ENNReal.tsum_le_tsum (fun n => (hpieces n).2)
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

theorem smooth_curve_coarea_bound
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t, (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  have hbound (n : ℕ) := smooth_curve_coarea_add_error hcoarea hD hA hAD hfin hf
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothCurveMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual differential-weighted curve fibers is
inherited from the published Lipschitz pieces and countable additivity. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem aemeasurable_smooth_curve_fiber
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    AEMeasurable (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) volume := by
  obtain ⟨U, L, hU, hcover, _, hLip, _⟩ := exists_countable_derivative_cover hD hf zero_lt_one
  let E : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hE (n : ℕ) : MeasurableSet (E n) :=
    hA.inter (MeasurableSet.disjointed (fun n => (hU n).measurableSet) n)
  have hEU (n : ℕ) : E n ⊆ U n := fun z hz => disjointed_subset U n hz.2
  have hEA (n : ℕ) : E n ⊆ A := inter_subset_left
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have hEq : (⋃ n, E n) = A := by
    ext z
    simp only [E, ← inter_iUnion, iUnion_disjointed, mem_inter_iff]
    exact ⟨And.left, fun hz => ⟨hz, hcover (hAD hz)⟩⟩
  have hm (n : ℕ) := (curve_coarea_lipschitzOn hcoarea (hE n)
    ((measure_mono (hEA n)).trans_lt hfin) ((hLip n).mono (hEU n))).1
  have hlevel (n : ℕ) (t : ℝ) : MeasurableSet (E n ∩ f ⁻¹' {t}) := by
    obtain ⟨g, hg, he⟩ := ((hLip n).mono (hEU n)).extend_real
    have heq : E n ∩ f ⁻¹' {t} = E n ∩ g ⁻¹' {t} := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact and_congr_right (fun hz => by rw [he hz])
    rw [heq]
    exact (hE n).inter (hg.continuous.measurable (measurableSet_singleton t))
  have heq : (fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})) =
      (fun t => ∑' n, (μH[0] : Measure ℂ) (E n ∩ f ⁻¹' {t})) := by
    funext t
    rw [← hEq, iUnion_inter]
    apply measure_iUnion
    · intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    · exact fun n => hlevel n t
  rw [heq]
  exact AEMeasurable.tsum hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothPathIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth scalar differential bounds distinct curve intersections,
including levels modulo one. The bound uses the actual curve image and
is obtained from Lipschitz coarea. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem smooth_curve_mod_one_coarea_bound
    (hcoarea : PlanarLipschitzFiberCoarea)
    {D A : Set ℂ} (hD : IsOpen D) (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hfin : (μH[1] : Measure ℂ) A < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      (μH[0] : Measure ℂ) (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) ≤
      ∫⁻ z in A, ENNReal.ofReal ‖fderiv ℝ f z‖ ∂(μH[1] : Measure ℂ) := by
  let L : ℝ → ℝ≥0∞ := fun t => (μH[0] : Measure ℂ) (A ∩ f ⁻¹' {t})
  have hm : AEMeasurable L volume := aemeasurable_smooth_curve_fiber hcoarea hD hA hAD hfin hf
  have hpoint (t : ℝ) :
      (μH[0] : Measure ℂ) (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) ≤
        periodizedLevelLength L t := by
    rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
    exact measure_iUnion_le _
  exact (lintegral_mono hpoint).trans
    ((lintegral_periodizedLevelLength_of_aemeasurable L hm).le.trans
      (smooth_curve_coarea_bound hcoarea hD hA hAD hfin hf))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedPhysicalChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted local chart estimates for actual quotient paths. The inverse
chart distortion is kept explicit; the length is the existing physical
occupation, with its original parameter multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physical_chart_length_measure_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure ℂ).restrict (A ∩ (π ∘ φ) ⁻¹' range γ.val) ≤
      (B : ℝ≥0∞) • ((dyadicPhysicalOccupation e y₀ γ).restrict (φ '' A)).map j := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply hjm hS,
    Measure.restrict_apply (hjm hS), smul_eq_mul]
  let E := S ∩ (A ∩ (π ∘ φ) ⁻¹' range γ.val)
  have hEA : E ⊆ A := fun _ h => h.2.1
  have hid : j '' (φ '' E) = E := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hj z (hEA hz)]
    · intro hw
      exact ⟨φ w, ⟨w, hw, rfl⟩, hj w (hEA hw)⟩
  calc
    (μH[1] : Measure ℂ) E = (μH[1] : Measure ℂ) (j '' (φ '' E)) := congrArg _ hid.symm
    _ ≤ (B : ℝ≥0∞) * (μH[1] : Measure Y) (φ '' E) := by
      simpa only [ENNReal.rpow_one] using
        (hB.mono (image_mono hEA)).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ (B : ℝ≥0∞) * dyadicPhysicalOccupation e y₀ γ (j ⁻¹' S ∩ φ '' A) := by
      apply mul_le_mul' le_rfl
      calc
        (μH[1] : Measure Y) (φ '' E) ≤ (μH[1] : Measure Y)
            ((j ⁻¹' S ∩ φ '' A) ∩ ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) := by
          apply measure_mono
          rintro _ ⟨z, hz, rfl⟩
          refine ⟨⟨?_, ⟨z, hEA hz, rfl⟩⟩, ?_⟩
          · change j (φ z) ∈ S
            rw [hj z (hEA hz)]
            exact hz.1
          · exact physical_chart_image_subset e y₀ π he φ hA γ.val ⟨z, hz.2, rfl⟩
        _ = ((μH[1] : Measure Y).restrict
            ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) (j ⁻¹' S ∩ φ '' A) :=
          (Measure.restrict_apply ((hjm hS).inter hφA)).symm
        _ ≤ _ := physical_image_hausdorff_le_occupation e hU y₀ γ _

theorem physical_chart_lintegral_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in A ∩ (π ∘ φ) ⁻¹' range γ.val, g z ∂(μH[1] : Measure ℂ)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, g (j y) ∂dyadicPhysicalOccupation e y₀ γ := by
  have h := lintegral_mono'
    (physical_chart_length_measure_le e hU y₀ π he φ hA j hjm hj B hB hφA γ)
    (fun z => le_refl (g z))
  rwa [lintegral_smul_measure, lintegral_map hg hjm, smul_eq_mul] at h

theorem smooth_physical_chart_image_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    volume (f '' (A ∩ (π ∘ φ) ⁻¹' range γ.val)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  have hlen := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA γ
  have hfin : (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) < ∞ := by
    apply hlen.trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ γ]
    exact (measure_mono (subset_univ _)).trans_lt (by
      rw [dyadicPhysicalOccupation_univ]
      exact γ.property)
  have hE := hA.inter
    (((isCompact_range γ.val.continuous).isClosed.preimage (hπ.comp hφ)).measurableSet)
  exact (smooth_curve_image_bound hD hE
    (inter_subset_left.trans hAD) hfin hf).trans
      (physical_chart_lintegral_le e hU y₀ π he φ hAG j hjm hj B hB hφA γ
        (fun z => ENNReal.ofReal ‖fderiv ℝ f z‖)
        (measurable_fderiv ℝ f).norm.ennreal_ofReal)

/-- The same weighted estimate for the actual quotient-coordinate image. -/
theorem quotient_smooth_image_le_physical (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (F : X → ℝ) (Q : Set X) (hF : ∀ z ∈ A, F (π (φ z)) = f z)
    (hcover : ∀ x ∈ range γ.val ∩ Q, ∃ z ∈ A, π (φ z) = x) :
    volume (F '' (range γ.val ∩ Q)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  apply (measure_mono ?_).trans
    (smooth_physical_chart_image_le e hU y₀ π hπ he φ hφ hA hφA hAG hAD hD j hjm hj B hB γ hf)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hcover x hx
  exact ⟨z, ⟨hz, by change π (φ z) ∈ range γ.val; rw [hzx]; exact hx.1⟩, (hF z hz).symm.trans (congrArg F hzx)⟩

theorem smooth_physical_chart_circle_count_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ.val) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  let E := A ∩ (π ∘ φ) ⁻¹' range γ.val
  have hE : MeasurableSet E := hA.inter
    (((isCompact_range γ.val.continuous).isClosed.preimage (hπ.comp hφ)).measurableSet)
  have hlen := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA γ
  have hfin : (μH[1] : Measure ℂ) E < ∞ := by
    apply hlen.trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ γ]
    exact (measure_mono (subset_univ _)).trans_lt (by
      rw [dyadicPhysicalOccupation_univ]
      exact γ.property)
  have hpoint (t : ℝ) := pathImageCount_image_le_hausdorffZero (π ∘ φ)
    (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) γ.val
  have hcount := lintegral_mono hpoint (μ := volume.restrict (Ico (0 : ℝ) 1))
  have heq (t : ℝ) :
      (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) ∩
        (π ∘ φ) ⁻¹' range γ.val =
      E ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)} := by
    ext z
    simp only [E, mem_inter_iff]
    tauto
  simp_rw [heq] at hcount
  exact hcount.trans ((smooth_curve_mod_one_coarea_bound hcoarea hD hE
    (inter_subset_left.trans hAD) hfin hf).trans
      (physical_chart_lintegral_le e hU y₀ π he φ hAG j hjm hj B hB hφA γ
        (fun z => ENNReal.ofReal ‖fderiv ℝ f z‖)
        (measurable_fderiv ℝ f).norm.ennreal_ofReal))

variable [MeasurableSpace X] [BorelSpace X]

theorem quotient_smooth_interval_image_le_physical
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {r s : PathTime} (hrs : r < s)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (F : X → ℝ) (Q : Set X) (hF : ∀ z ∈ A, F (π (φ z)) = f z)
    (hcover : ∀ x ∈ γ.val '' Icc r s ∩ Q, ∃ z ∈ A, π (φ z) = x) :
    volume (F '' (γ.val '' Icc r s ∩ Q)) ≤
      ∫⁻ t in Icc r s, (B : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) (physicalValue e y₀ (γ.val t))
        ∂physicalTimeLength e y₀ γ := by
  let g : Y → ℝ≥0∞ := fun y => (B : ℝ≥0∞) *
    (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) y
  have hg : Measurable g := measurable_const.mul
    ((((measurable_fderiv ℝ f).norm.ennreal_ofReal).comp hjm).indicator hφA)
  have hrange : range (affineFinitePhysicalPath e hU y₀ γ hrs).val = γ.val '' Icc r s :=
    intervalPath_range γ.val hrs
  have hp := quotient_smooth_image_le_physical e hU y₀ π hπ he φ hφ hA hφA
    hAG hAD hD j hjm hj B hB (affineFinitePhysicalPath e hU y₀ γ hrs) hf F Q hF
    (by simpa only [hrange] using hcover)
  rw [hrange] at hp
  have heq : (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀
      (affineFinitePhysicalPath e hU y₀ γ hrs)) =
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hrs) := by
    rw [show g = fun y => (B : ℝ≥0∞) *
      (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) y from rfl,
      lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_indicator hφA]
  rw [← heq, physicalCost_affine e hU y₀ γ hrs g hg] at hp
  exact hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RealBandPhysicalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singleton-contact argument gives a physical payment
inequality on every retained parameter interval. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r5b7c64_2 : BorelSpace Sphere := ⟨rfl⟩
theorem real_band_interval_physical_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {r s : PathTime} (hrs : r < s)
    (hγV : γ.val '' Icc r s ⊆ V)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ γ.val '' Icc r s ∩ D, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ.val r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ.val s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ.val '' Icc r s ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ physicalTagPayment e y₀ γ
      (fun y => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y) m (Icc r s) := by
  have hp := real_band_interval_image_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf γ.val hrs hγV m hm ha hb hbranch hfree
  have hi := quotient_smooth_interval_image_le_physical e hU y₀ π hπ he φ hφ hA hφA
    hAG hAO hO j hjm hj L hL γ hrs hv f D hvf hcover
  exact hp.trans (by
    change _ ≤ tagPaymentMeasure (physicalTimeLength e y₀ γ)
      (fun t => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) (physicalValue e y₀ (γ.val t))) γ.val m (Icc r s)
    rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ measurableSet_Icc]
    exact add_le_add hi le_rfl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBandTagNullTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null free traces inside a tag: the local variation estimate and its
finite physical-plus-visit payment measure are both constructed above. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r5b7c64_3 : BorelSpace Sphere := ⟨rfl⟩
theorem real_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {T : Set PathTime} (hT : IsOpen T)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ range γ.val ∩ D ∩ V, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    (hmFree : ∀ z ∈ B \ Flags, m z = 0) (hBU : B ⊆ Uᶜ)
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (B \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T,
      γ.val t ∈ B \ Flags → (γ.val t, θ) ∈ circleBandGraph D f →
      ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} (γ.val t)).Nontrivial)
    (hcost : (∫⁻ y, (L : ℝ≥0∞) * (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y ∂dyadicPhysicalOccupation e y₀ γ) +
      boundaryToll γ.val m < ∞) :
    volume ((trace ∘ γ.val) ''
      ((γ.val ⁻¹' (B \ Flags)) ∩ (T ∩ γ.val ⁻¹' V))) = 0 := by
  let g : Sphere → ℝ≥0∞ := fun y => (L : ℝ≥0∞) * (φ '' A).indicator
    (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y
  have hg : Measurable g := measurable_const.mul
    ((((measurable_fderiv ℝ v).norm.ennreal_ofReal).comp hjm).indicator hφA)
  let κ := physicalTagPayment e y₀ γ g m
  let : IsFiniteMeasure κ := physicalTagPayment_finite e hU y₀ γ g hg m hcost
  have hF : MeasurableSet (γ.val ⁻¹' (B \ Flags)) :=
    γ.val.continuous.measurable (hB.measurableSet.diff hFlags.measurableSet)
  have hκF : κ (γ.val ⁻¹' (B \ Flags)) = 0 :=
    physicalTagPayment_null_free e hU y₀ γ g m hF
      (fun t ht => hBU ht.1) (fun t ht => hmFree (γ.val t) ht)
  apply path_time_null_image_of_interval_payment κ
    (hT.inter (hV.preimage γ.val.continuous))
    (measure_mono_null inter_subset_left hκF) (trace ∘ γ.val)
  intro r hr' s hs' hrs hI
  rcases hrs.eq_or_lt with hrs | hrs
  · subst s
    simp only [comp_apply, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hp := real_band_interval_physical_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf e hU y₀ he φ hφ hA hφA
      hAG hAO hO j hjm hj L hL γ hrs
      (by
        rintro x ⟨t, ht, rfl⟩
        exact (hI ht).2)
      hv hvf
      (by
        rintro x ⟨⟨t, ht, rfl⟩, hxD⟩
        exact hcover (γ.val t) ⟨⟨mem_range_self t, hxD⟩, (hI ht).2⟩)
      m hm (htrace (γ.val r) ⟨hr'.1, hr'.2.2⟩)
      (htrace (γ.val s) ⟨hs'.1, hs'.2.2⟩) hbranch ?_
    · exact hp
    · filter_upwards [hgood] with θ hθ
      rintro z ⟨⟨t, ht, htz⟩, hz⟩ hfree
      subst z
      exact hθ t (hI ht).1 hfree hz

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalBallArea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic local area growth for the fixed physical sphere metric, at
finite points. This compares its actual chart with the area chart. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem sphericalAreaDensity_le_four (z : ℂ) : sphericalAreaDensity z ≤ 4 := by
  rw [sphericalAreaDensity, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ ^ 2)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereChartInversePairs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse chart control for pairs of nearby finite sphere points. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem linear_stereo_inverse_pairs (v : RoundAmbient) (hv : ‖v‖ = 1)
    (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (stereoInvFunAux v (A z : RoundAmbient)) ∧
      ∀ w u : ℂ, stereoInvFunAux v (A w : RoundAmbient) ∈ W →
        stereoInvFunAux v (A u : RoundAmbient) ∈ W →
        dist w u ≤ L * dist (stereoInvFunAux v (A w : RoundAmbient))
          (stereoInvFunAux v (A u : RoundAmbient)) := by
  let F : ℂ → RoundAmbient := fun w => stereoInvFunAux v (A w : RoundAmbient)
  let g : RoundAmbient → ℂ := fun x => A.symm (stereoToFun v x)
  have hleft (w : ℂ) : g (F w) = w := by
    change A.symm (stereoToFun v (stereoInvFun hv (A w))) = w
    rw [stereo_right_inv, A.symm_apply_apply]
  have hx : ‖F z‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv (A z).property)
  have hneq : innerSL ℝ v (F z) ≠ 1 := by
    intro h
    have he : v = F z := (inner_eq_one_iff_of_norm_eq_one hv hx).mp h
    exact stereoInvFun_ne_north_pole hv (A z) (Subtype.ext he.symm)
  have hopen : IsOpen {x : RoundAmbient | innerSL ℝ v x ≠ 1} :=
    (isClosed_eq (innerSL ℝ v).continuous continuous_const).isOpen_compl
  have hg : ContDiffAt ℝ 1 g (F z) :=
    A.symm.contDiff.contDiffAt.comp (F z)
      ((contDiffOn_stereoToFun (n := 1)).contDiffAt (hopen.mem_nhds hneq))
  obtain ⟨L, W, hW, hL⟩ := hg.exists_lipschitzOnWith
  refine ⟨L, W, hW, fun w u hw hu => ?_⟩
  simpa only [hleft] using hL.dist_le_mul (F w) hw (F u) hu

theorem finite_sphere_chart_inverse_pairs (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (roundSphereEquiv (z : Sphere) : RoundAmbient) ∧
      ∀ w u : ℂ, (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W →
        (roundSphereEquiv (u : Sphere) : RoundAmbient) ∈ W →
        dist w u ≤ L * dist (roundSphereEquiv (w : Sphere) : RoundAmbient)
          (roundSphereEquiv (u : Sphere) : RoundAmbient) := by
  classical
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply linear_stereo_inverse_pairs
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereSliceChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite physical point has a chart neighborhood with a concrete
inverse Lipschitz bound. This is used only on compact coordinate slices. -/

open Set Function Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

 theorem exists_sphereSliceChart (z : ℂ) :
    ∃ (B : ℝ≥0) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' V) := by
  obtain ⟨B, W, hW, hB⟩ := finite_sphere_chart_inverse_pairs z
  have hc : Continuous (fun w : ℂ => (roundSphereEquiv (w : Sphere) : RoundAmbient)) :=
    continuous_subtype_val.comp (roundSphereEquiv.continuous.comp OnePoint.continuous_coe)
  obtain ⟨V, hVW, hV, hzV⟩ := _root_.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  refine ⟨B, V, hV, hzV, LipschitzOnWith.of_dist_le_mul ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨u, hu, rfl⟩
  change dist w u ≤ (B : ℝ) *
    dist (roundSphereEquiv (w : Sphere) : RoundAmbient) (roundSphereEquiv (u : Sphere) : RoundAmbient)
  exact hB w u (hVW hw) (hVW hu)

 theorem finiteCoord_lipschitz_on_compact_chart {A : Set ℂ} (hA : IsCompact A) :
    ∃ B : ℝ≥0, LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' A) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hA.image OnePoint.continuous_coe)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨B, V, hV, hzV, hBV⟩ := exists_sphereSliceChart z
  refine ⟨B, ((↑) : ℂ → Sphere) '' V, mem_nhdsWithin_of_mem_nhds ?_, hBV⟩
  exact (OnePoint.isOpenEmbedding_coe.isOpenMap V hV).mem_nhds ⟨z, hzV, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SphericalChartCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-integrable planar derivatives give the finite spherical
weights used by each local tag payment measure. The inverse chart is
Borel, including its arbitrary value at infinity. -/

open Set Function MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_7
theorem measurable_finiteCoord : Measurable finiteCoord := by
  classical
  obtain ⟨j, hj, he⟩ := OnePoint.isOpenEmbedding_coe.measurableEmbedding.exists_measurable_extend
    (measurable_id (α := ℂ)) (fun _ => inferInstance)
  have hfun : ({OnePoint.infty} : Set Sphere).piecewise (fun _ => (0 : ℂ)) j = finiteCoord := by
    funext p
    cases p using OnePoint.rec with
    | infty => simp [finiteCoord]
    | coe z =>
      simpa only [mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true, piecewise_eq_of_notMem,
        finiteCoord_coe, comp_apply, id_eq] using congrFun he z
  rw [← hfun]
  exact measurable_const.piecewise (measurableSet_singleton _) hj

theorem measurable_localizedSphericalChartWeight (L : ℝ≥0) {A : Set ℂ}
    (hA : MeasurableSet A) {k : ℂ → ℝ≥0∞} (hk : Measurable k) :
    Measurable (localizedSphericalChartWeight L A k) :=
  measurable_const.mul ((hk.comp measurable_finiteCoord).indicator
    (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA))

theorem localizedSphericalChartWeight_coe (L : ℝ≥0) (A : Set ℂ) (k : ℂ → ℝ≥0∞) (z : ℂ) :
    localizedSphericalChartWeight L A k (z : Sphere) = (L : ℝ≥0∞) * A.indicator k z := by
  classical
  by_cases hz : z ∈ A <;> simp [localizedSphericalChartWeight, hz]

theorem localizedSphericalChartWeight_square_finite (L : ℝ≥0) {A : Set ℂ}
    (hA : MeasurableSet A) {k : ℂ → ℝ≥0∞} (hk : Measurable k)
    (henergy : (∫⁻ z in A, k z ^ 2) < ∞) :
    (∫⁻ y, localizedSphericalChartWeight L A k y ^ 2 ∂sphericalArea) < ∞ := by
  rw [lintegral_sphericalArea _ ((measurable_localizedSphericalChartWeight L hA hk).pow_const 2)]
  simp_rw [localizedSphericalChartWeight_coe]
  have hb : (∫⁻ z, ENNReal.ofReal (sphericalAreaDensity z) * ((L : ℝ≥0∞) * A.indicator k z) ^ 2) ≤
      (4 : ℝ≥0∞) * (L : ℝ≥0∞) ^ 2 * ∫⁻ z in A, k z ^ 2 := by
    calc
      _ ≤ ∫⁻ z, ((4 : ℝ≥0∞) * (L : ℝ≥0∞) ^ 2) * A.indicator (fun z => k z ^ 2) z := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ A
        · simp only [indicator_of_mem hz, mul_pow]
          have hD : ENNReal.ofReal (sphericalAreaDensity z) ≤ 4 :=
            (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four z)).trans_eq (by norm_num)
          simpa only [mul_assoc] using mul_le_mul' hD (le_refl ((L : ℝ≥0∞) ^ 2 * k z ^ 2))
        · simp only [indicator_of_notMem hz, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          exact le_rfl
      _ = _ := by rw [lintegral_const_mul' _ _ (by finiteness), lintegral_indicator hA]
  exact hb.trans_lt (ENNReal.mul_lt_top (by finiteness) henergy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_QuotientLocalChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quotient neighborhood whose closure misses the image of infinity
has a bounded inverse physical chart. Domain points in it are covered
by that chart using the actual domain homeomorphism. -/

open Set Function
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

theorem finiteCoord_lipschitz_quotient_neighborhood
    (π : Sphere → Sphere) (hπ : Continuous π) (G V : Set Sphere)
    (hinfty : π OnePoint.infty ∉ closure V) :
    ∃ L : ℝ≥0, LipschitzOnWith L finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V)) := by
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure V)) :=
    isCompact_finite_preimage (isClosed_closure.preimage hπ) hinfty
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_on_compact_chart hK
  refine ⟨L, hL.mono (image_mono ?_)⟩
  intro z hz
  exact subset_closure hz.2

theorem quotient_neighborhood_chart_covers
    {G U V : Set Sphere} (e : G ≃ₜ U) (π : Sphere → Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (hinfty : π OnePoint.infty ∉ V) :
    ∀ x ∈ U ∩ V, ∃ z : ℂ,
      z ∈ (((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) ∧
      π (z : Sphere) = x := by
  intro x hx
  let y := e.symm ⟨x, hx.1⟩
  have hy : π y.val = x := by rw [← he y]; exact congrArg Subtype.val (e.apply_symm_apply _)
  have hyG : y.val ∈ G := y.property
  cases hp : y.val using OnePoint.rec with
  | infty =>
    have hyV : π y.val ∈ V := hy.symm ▸ hx.2
    exact (hinfty (by simpa only [hp] using hyV)).elim
  | coe z =>
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_preimage, ← hp] using hyG
    · change π (z : Sphere) ∈ V
      rw [← hp, hy]
      exact hx.2
    · rw [← hp]
      exact hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LawRealBandTagNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Application of the local tag proof to a physical path law. The
inverse-chart bound and the finite payment measure are constructed from
the quotient neighborhood, the differential energy and the law's density.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_4 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_parameter_real_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {G U V Flags : Set Sphere} (hG : IsOpen G) (hU : IsOpen U) (hdense : Dense U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (e : G ≃ₜ U) (y₀ : Sphere) (he : ∀ y : G, (e y).val = π y.val)
    (hTD : IsTotallyDisconnected Uᶜ) (hbad : ∀ p ∈ Gᶜ, π p ∈ Uᶜ)
    (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ closure V) (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ U, |f z| ≤ M) (hf : ContinuousOn f U)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' G))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, Sphere)) (hγmap : Measurable γmap)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (hμ : P.map (f := γmap) (by first | exact hγmap.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = μ)
    (hfinite : ∀ᵐ z ∂(P : Measure Z), physicalDomainLength e y₀ (γmap z) < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞)
    (hband : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[U] z) - liminf f (𝓝[U] z)) ≤ m z)
    (hmFree : ∀ z ∈ Uᶜ \ Flags, m z = 0)
    (T : Z → Set PathTime) (hT : ∀ z, IsOpen (T z))
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (Uᶜ \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T z,
      γmap z t ∈ Uᶜ \ Flags → (γmap z t, θ) ∈ circleBandGraph U f →
      ¬ (connectedComponentIn {x | (x, θ) ∈ circleBandGraph U f} (γmap z t)).Nontrivial) :
    ∀ᵐ z ∂(P : Measure Z), volume ((trace ∘ γmap z) ''
      ((γmap z ⁻¹' (Uᶜ \ Flags)) ∩ (T z ∩ γmap z ⁻¹' V))) = 0 := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := O ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖fderiv ℝ v z‖
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hA : MeasurableSet A := (hO.inter (hV.preimage (hπ.comp OnePoint.continuous_coe))).measurableSet
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_quotient_neighborhood π hπ G V hinfty
  let g := localizedSphericalChartWeight L A k
  have hk : Measurable k := (measurable_fderiv ℝ v).norm.ennreal_ofReal
  have hg : Measurable g := measurable_localizedSphericalChartWeight L hA hk
  have hg2 : (∫⁻ y, g y ^ 2 ∂sphericalArea) < ∞ :=
    localizedSphericalChartWeight_square_finite L hA hk
      ((lintegral_mono_set inter_subset_left).trans_lt henergy)
  have hcost := ae_physical_and_visit_cost_finite e hU y₀ μ sphericalArea ρ g hρ hg hocc
    hρ2 hg2 m hm hweight hvisits
  have hcostZ : ∀ᵐ z ∂(P : Measure Z),
      (∫⁻ y, g y ∂physicalOccupationCode e y₀ (γmap z)) + boundaryToll (γmap z) m < ∞ := by
    have hmap : (P : Measure Z).map γmap = (μ : Measure C(PathTime, Sphere)) := by
      rw [← ProbabilityMeasure.toMeasure_map P hγmap.aemeasurable, hμ]
    exact ae_of_ae_map hγmap.aemeasurable (hmap.symm ▸ hcost)
  filter_upwards [hfinite, hcostZ, hgood] with z hγ hc hγgood
  let γp : FinitePhysicalPath e y₀ := ⟨γmap z, hγ⟩
  rw [physicalOccupationCode_eq e y₀ γp] at hc
  exact real_band_tag_null_trace (B := Uᶜ) (D := U) hsard hsch G π hπ hclosed hsurj hr
    hU.isClosed_compl hTD hbad (by simpa only [compl_compl] using (Subset.rfl : U ⊆ U)) hdense hU hV
    (fun h => hinfty (subset_closure h)) hFlags hM hf e hU y₀ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA
    (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA)
    (fun _ hz => hz.1) inter_subset_left hO finiteCoord measurable_finiteCoord
    (fun z _ => finiteCoord_coe z) L hL γp (hT z) hv (fun _ _ => rfl)
    (fun x hx => quotient_neighborhood_chart_covers e π he
      (fun h => hinfty (subset_closure h)) x ⟨hx.1.2, hx.2⟩)
    m hband hmFree (fun _ hx => hx) trace htrace hbranch hγgood hc

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_NullLevelTuples
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null sets of scalar levels induce null sets of finite tagged tuples.
This also supplies a Borel description when the null sets are envelopes. -/

open Set Function MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem measurableEmbedding_tupleFiber (i : TupleType) : MeasurableEmbedding (tupleFiber i) := by
  apply (measurable_tupleFiber i).measurableEmbedding
  intro x y h
  have hp : (i.2, x) = (i.2, y) :=
    sigma_mk_injective (β := fun n : ℕ =>
      (Fin (n + 1) → ℕ) × (Fin (n + 1) → UnitAddCircle)) h
  exact congrArg Prod.snd hp

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_slots_zero_on_null_tuples (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k, slotTupleMeasure (Γ.val.2 k) A = 0 := by
  apply ae_all_iff.mpr
  intro k
  have h := slotLaw_absolutelyContinuous d P τ hτ k hz
  rw [slotLaw_apply d P k hA] at h
  exact (lintegral_eq_zero_iff ((Measure.measurable_coe hA).comp
    (measurable_baseCodeSlot d k))).mp h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SlotPairNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent active tag tuples avoid every product-null tuple event.
Inactive slots carry no tuple mass. -/

open Set Filter Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem ae_active_slots_avoid (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (τ : Measure LevelTuple)
    (hτ : meanCodeTuple d P ≪ τ) (A : Set LevelTuple) (hA : MeasurableSet A)
    (hz : τ A = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k q,
      Γ.val.2 k = Sum.inr q → tagDataTuple q ∉ A := by
  filter_upwards [ae_slots_zero_on_null_tuples d P τ hτ A hA hz] with Γ hΓ
  intro k q hq hmem
  have h := hΓ k
  rw [hq, slotTupleMeasure, Sum.elim_inr, Measure.dirac_apply' _ hA,
    indicator_of_mem hmem, Pi.one_apply] at h
  exact one_ne_zero h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TorusProjection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection onto any distinct selection of finite circle coordinates
preserves normalized Haar measure. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem torus_projection_measurePreserving {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Injective e) :
    MeasurePreserving (fun θ : I → UnitAddCircle => θ ∘ e) volume volume := by
  let f : (I → UnitAddCircle) →+ (J → UnitAddCircle) :=
    { toFun := fun θ => θ ∘ e
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hsurj : Surjective f := by
    intro θ
    refine ⟨Function.extend e θ (fun _ => 0), ?_⟩
    funext j
    exact he.extend_apply θ (fun _ => 0) j
  apply AddMonoidHom.measurePreserving (f := f)
    (by exact continuous_pi fun j => continuous_apply (e j)) hsurj
  change (Measure.pi (fun _ : I => (volume : Measure UnitAddCircle))) univ =
    (Measure.pi (fun _ : J => (volume : Measure UnitAddCircle))) univ
  simp [Measure.pi_univ, AddCircle.measure_univ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TuplePairCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent tuples satisfy every ordered compatibility test and have
no equal levels carrying the same label across the two tuples. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

variable {X : Type*} [TopologicalSpace X]

theorem ae_torus_pair_distinct {n m : ℕ} :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))), ∀ i j, p.1 i ≠ p.2 j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hd : ((volume : Measure UnitAddCircle).prod volume)
      {p : UnitAddCircle × UnitAddCircle | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (isClosed_eq continuous_fst continuous_snd).measurableSet]
    have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
      simpa only [image_singleton, AddCircle.coe_zero] using
        (volume_addCircle_image_eq_zero (A := {(0 : ℝ)}) (measure_singleton 0))
    simp [hz]
  have hp := (measurePreserving_eval (fun _ : Fin n => (volume : Measure UnitAddCircle)) i).prod
    (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j)
  have hgood : ∀ᵐ p ∂((volume : Measure UnitAddCircle).prod volume), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_not] using hd
  exact hp.quasiMeasurePreserving.ae hgood

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TagComponents
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonconstant active tag lies in a nontrivial connected component
through each of its interior image points. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem nontrivial_component_of_tag (γ : C(PathTime, X)) (s : TagSlot)
    (hshape : (γ, s) ∈ validTagShape) (A : Set X)
    (hcontain : ∀ t, tagLeft s < t → t < tagRight s → γ t ∈ A)
    (t : PathTime) (hl : tagLeft s < t) (hr : t < tagRight s) :
    (connectedComponentIn A (γ t)).Nontrivial := by
  have hnonconstant : (γ, s) ∈ nonconstantTagSegment := by
    rcases hshape with h | h
    · obtain ⟨u, hu⟩ := h
      change Sum.inl u = s at hu
      rw [← hu] at hl
      exact (not_lt_of_ge le_top hl).elim
    · exact h
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := hnonconstant
  have hconn : IsPreconnected (γ '' Ioo (tagLeft s) (tagRight s)) :=
    isPreconnected_Ioo.image γ γ.continuous.continuousOn
  have hsub : γ '' Ioo (tagLeft s) (tagRight s) ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hcontain u hu.1 hu.2
  have hcc := hconn.subset_connectedComponentIn (mem_image_of_mem γ ⟨hl, hr⟩) hsub
  exact ⟨γ a, hcc (mem_image_of_mem γ ⟨ha, ha'⟩),
    γ b, hcc (mem_image_of_mem γ ⟨hb, hb'⟩), hab⟩

omit [T2Space X] in
theorem active_tag_nontrivial_component
    (H : ℕ → Set (UnitAddCircle × X)) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q)) :
    (connectedComponentIn (⋃ j : Fin (q.1 + 1), {x | (q.2.2.1 j, x) ∈ H (q.2.1 j)})
      (γ t)).Nontrivial := by
  apply nontrivial_component_of_tag γ (Sum.inr q) hshape _ _ t hl hr
  intro u hu hu'
  exact mem_iUnion.mpr (hcontain u hu hu')

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_IndependentTagLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute continuity of tag tuples supplies the independent-level
singleton conclusion for almost every path and almost every level. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem tupleReference_product_right_null
    {T : Type*} [MeasurableSpace T] (ω : TupleType → ℝ≥0∞)
    (ν : Measure T) [SFinite ν] (E : Set (LevelTuple × T))
    (hE : ∀ i : TupleType,
      ((volume : Measure (Fin (i.1 + 1) → UnitAddCircle)).prod ν)
        (Prod.map (tupleFiber i) id ⁻¹' E) = 0) :
    ((tupleReference ω).prod ν) E = 0 := by
  rw [tupleReference, Measure.prod_sum_left, Measure.sum_apply_eq_zero]
  intro i
  rw [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  have hm := Measure.map_prod_map
    (volume : Measure (Fin (i.1 + 1) → UnitAddCircle)) ν
    (measurable_tupleFiber i) (measurable_id (α := T))
  rw [Measure.map_id] at hm
  rw [hm, ((measurableEmbedding_tupleFiber i).prodMap MeasurableEmbedding.id).map_apply,
    hE, mul_zero]

private theorem measurableSet_activeSlotParameterEvent
    {T : Type*} [MeasurableSpace T] (E : Set (LevelTuple × T)) (hE : MeasurableSet E) :
    MeasurableSet (activeSlotParameterEvent E) := by
  let : MeasurableSpace TagData := borel TagData
  let : BorelSpace TagData := ⟨rfl⟩
  have hme : MeasurableEmbedding activeTagSlot :=
    Topology.IsOpenEmbedding.measurableEmbedding (α := TagData) (β := TagSlot)
      Topology.IsOpenEmbedding.inr
  have he : activeSlotParameterEvent E =
      Prod.map activeTagSlot id '' (Prod.map tagDataTuple id ⁻¹' E) := by
    ext p
    constructor
    · rintro ⟨q, hq, hmem⟩
      exact ⟨(q, p.2), hmem, Prod.ext hq.symm rfl⟩
    · rintro ⟨⟨q, t⟩, hmem, rfl⟩
      exact ⟨q, rfl, hmem⟩
  rw [he]
  exact (hme.prodMap MeasurableEmbedding.id).measurableSet_image.mpr
    (hE.preimage (continuous_tagDataTuple.measurable.prodMap measurable_id))

theorem ae_active_slots_avoid_independent_null
    {X Y T : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X]
    [MeasurableSpace C(PathTime, X)] [MeasurableSpace T]
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (τ : Measure LevelTuple) [SFinite τ] (ν : Measure T) [SFinite ν]
    (hτ : meanCodeTuple d P ≪ τ) (E : Set (LevelTuple × T))
    (hzero : (τ.prod ν) E = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ t ∂ν,
      ∀ k q, Γ.val.2 k = Sum.inr q → (tagDataTuple q, t) ∉ E := by
  obtain ⟨E', hEE', hE', hz⟩ := exists_measurable_superset_of_null hzero
  have hsections : ∀ᵐ t ∂ν, τ ((fun q => (q, t)) ⁻¹' E') = 0 := by
    rw [Measure.prod_apply_symm hE'] at hz
    exact (lintegral_eq_zero_iff (measurable_measure_prodMk_right hE')).mp hz
  have hpair (k : ℕ) : ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod ν),
      (p.1.val.2 k, p.2) ∉ activeSlotParameterEvent E' := by
    have hm : MeasurableSet {p : BasePathCode d × T |
        (p.1.val.2 k, p.2) ∉ activeSlotParameterEvent E'} :=
      (measurableSet_activeSlotParameterEvent E' hE').compl.preimage
        (((measurable_pi_apply k).comp (measurable_snd.comp
          (measurable_subtype_coe.comp measurable_fst))).prodMk measurable_snd)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    have hreverse : ∀ᵐ t ∂ν, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        (Γ.val.2 k, t) ∉ activeSlotParameterEvent E' := by
      filter_upwards [hsections] with t ht
      filter_upwards [ae_active_slots_avoid d P τ hτ
        ((fun q => (q, t)) ⁻¹' E')
        (hE'.preimage (measurable_id.prodMk measurable_const)) ht] with Γ hΓ
      rintro ⟨q, hq, hqt⟩
      exact hΓ k q hq hqt
    exact (Measure.ae_ae_comm hm).mpr hreverse
  have hall := ae_all_iff.mpr hpair
  have hfull : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ t ∂ν,
      ∀ k, (Γ.val.2 k, t) ∉ activeSlotParameterEvent E' :=
    Measure.ae_ae_of_ae_prod hall
  filter_upwards [hfull] with Γ hΓ
  filter_upwards [hΓ] with t ht
  intro k q hq hmem
  exact ht k ⟨q, hq, hEE' hmem⟩

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
-- module Solutions.Q146_CD.CircleDomains_Topology_FreeBandNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero band budget produces the actual unique trace, and narrow
neighborhoods can be chosen with closure in a prescribed chart region. -/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem real_band_fiber_eq_trace_of_zero_width
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [FirstCountableTopology X] {D : Set X} {f : X → ℝ} {M : ℝ}
    (hM : ∀ z ∈ D, |f z| ≤ M) {x : X} (hx : x ∈ closure D)
    (hwidth : limsup f (𝓝[D] x) - liminf f (𝓝[D] x) ≤ 0) :
    ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = realBoundaryTrace D f x := by
  have he := intervalFiberHull_clusterGraph_eq_boundary_band hM hx
  obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM hx
  have hh := subset_intervalFiberHull (clusterGraph D f) ht
  have hi : liminf f (𝓝[D] x) ≤ limsup f (𝓝[D] x) := by
    have hmem : t ∈ Icc (liminf f (𝓝[D] x)) (limsup f (𝓝[D] x)) := he ▸ hh
    exact hmem.1.trans hmem.2
  have heq : limsup f (𝓝[D] x) = liminf f (𝓝[D] x) := by linarith
  intro t
  change t ∈ {t | (x, t) ∈ intervalFiberHull (clusterGraph D f)} ↔ _
  rw [he, heq, Icc_self]
  rfl

theorem exists_narrow_real_band_neighborhood_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {D W : Set X} {f : X → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    {x : X} {a : ℝ} (hW : IsOpen W) (hxW : x ∈ W)
    (htrace : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ioo (a - ε) (a + ε) := by
  obtain ⟨V, hV, hxV, hv⟩ := exists_narrow_real_band_neighborhood hM htrace hε
  obtain ⟨Q, hQ, hxQ, hQV⟩ := normal_exists_closure_subset
    (isClosed_singleton : IsClosed ({x} : Set X)) (hV.inter hW)
      (singleton_subset_iff.mpr ⟨hxV, hxW⟩)
  refine ⟨Q, hQ, hxQ (mem_singleton x), hQV.trans inter_subset_right, ?_⟩
  intro y hy t ht
  exact hv y (hQV (subset_closure hy)).1 t ht

theorem countable_narrow_real_band_cover_closure
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X]
    {D F W : Set X} {f a : X → ℝ} {M : ℝ}
    (hM : ∀ z ∈ D, |f z| ≤ M) (hW : IsOpen W) (hFW : F ⊆ W)
    (htrace : ∀ x ∈ F, ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) → t = a x) :
    ∃ (S : Set X) (V : X → Set X), S ⊆ F ∧ S.Countable ∧
      F ⊆ ⋃ x ∈ S, V x ∧ ∀ x ∈ S,
        IsOpen (V x) ∧ x ∈ V x ∧ closure (V x) ⊆ W ∧
        ∀ y ∈ V x, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
          t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
  have hn : ∀ x ∈ F, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW, hv⟩ := exists_narrow_real_band_neighborhood_closure
      hM hW (hFW hx) (htrace x hx) (by norm_num : (0 : ℝ) < 1 / 4)
    refine ⟨V, hV, hxV, hVW, ?_⟩
    intro y hy t ht
    have hb := hv y hy t ht
    constructor <;> linarith [hb.1, hb.2]
  have hc : ∀ x, ∃ V : Set X, x ∈ F → IsOpen V ∧ x ∈ V ∧ closure V ⊆ W ∧
      ∀ y ∈ V, ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) →
        t ∈ Ico (a x - 1 / 2) (a x - 1 / 2 + 1) := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨V, hV⟩ := hn x hx
      exact ⟨V, fun _ => hV⟩
    · exact ⟨∅, fun h => (hx h).elim⟩
  choose V hV using hc
  obtain ⟨S, hSF, hSc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := F) (f := V) (fun x hx =>
      mem_nhdsWithin_of_mem_nhds ((hV x hx).1.mem_nhds (hV x hx).2.1))
  exact ⟨S, V, hSF, hSc, hcover, fun x hx => hV x (hSF hx)⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LocalBandPaidValues
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local real branches may describe a globally defined closed circle level
without extending continuously through its cut. The topological crossing is
performed in that global level; real values are used only inside the branch
neighborhood. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem local_band_paid_values
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M)
    (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b v c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hav : a < v) (hvb : v < b) (hv : v ∈ Ico c (c + 1))
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ z ∈ range γ ∩ H (v : UnitAddCircle), z ∈ B \ Flags →
      ¬ (connectedComponentIn (H (v : UnitAddCircle)) z).Nontrivial) :
    v ∈ f '' (range γ ∩ D) ∨
      ∃ z ∈ range γ ∩ Flags, (z, v) ∈ intervalFiberHull (clusterGraph D f) := by
  have hxV : x ∈ V := hγV ⟨0, γ.source⟩
  have hyV : y ∈ V := hγV ⟨1, γ.target⟩
  have hai := hbranch x hxV a ((ha a).mpr rfl)
  have hbi := hbranch y hyV b ((hb b).mpr rfl)
  have hxH : x ∉ H (v : UnitAddCircle) := by
    intro hx
    obtain ⟨⟨z, t⟩, ht, he⟩ := (hlevel x hxV _).mpr hx
    change (z, (t : UnitAddCircle)) = (x, (v : UnitAddCircle)) at he
    have hz : z = x := congrArg Prod.fst he
    subst z
    have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hbranch x hxV t ht) hv).mp (congrArg Prod.snd he)
    exact hav.ne' (htv.symm.trans ((ha t).mp ht))
  have hyH : y ∉ H (v : UnitAddCircle) := by
    intro hy
    obtain ⟨⟨z, t⟩, ht, he⟩ := (hlevel y hyV _).mpr hy
    change (z, (t : UnitAddCircle)) = (y, (v : UnitAddCircle)) at he
    have hz : z = y := congrArg Prod.fst he
    subst z
    have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (hbranch y hyV t ht) hv).mp (congrArg Prod.snd he)
    exact hvb.ne (htv.symm.trans ((hb t).mp ht))
  have hcl (z : Sphere) : z ∈ closure D := by rw [hdense.closure_eq]; trivial
  obtain ⟨z, hz, hp⟩ := singleton_free_contacts_force_paid_level hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad (hH _) hV hinfty
    (isCompact_intervalFiberHull (isCompact_clusterGraph hM))
    (fun z _ => by
      obtain ⟨t, ht⟩ := clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z)
      exact ⟨t, subset_intervalFiberHull _ ht⟩)
    (fun z _ => by
      rw [intervalFiberHull_fiber_eq_Icc (isCompact_clusterGraph hM) z
        (clusterGraph_fiber_nonempty_of_mem_closure hM (hcl z))]
      exact ordConnected_Icc)
    (fun z hz ht => (hlevel z hz _).mp ⟨(z, v), ht, rfl⟩)
    hxH hyH γ hγV ((ha a).mpr rfl) ((hb b).mpr rfl) hav.le hvb.le
    (Free := B \ Flags) (Paid := D ∪ Flags)
    (by
      intro z _
      by_cases hzB : z ∈ B
      · by_cases hzF : z ∈ Flags
        · exact Or.inr (Or.inr hzF)
        · exact Or.inl ⟨hzB, hzF⟩
      · exact Or.inr (Or.inl (hBD hzB))) hfree
  obtain ⟨⟨w, t⟩, ht, he⟩ := (hlevel z (hγV hz.1) _).mpr hz.2
  change (w, (t : UnitAddCircle)) = (z, (v : UnitAddCircle)) at he
  have hw : w = z := congrArg Prod.fst he
  subst w
  have htv := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (hbranch z (hγV hz.1) t ht) hv).mp (congrArg Prod.snd he)
  subst t
  rcases hp with hzD | hzF
  · have hcont : ContinuousAt f z := hf.continuousAt ((hD.inter hV).mem_nhds ⟨hzD, hγV hz.1⟩)
    obtain ⟨r, s, q, hr, hs, _, heq⟩ := mem_intervalFiberHull_iff.mp ht
    rw [clusterGraph_fiber_eq_of_continuousAt hcont hr,
      clusterGraph_fiber_eq_of_continuousAt hcont hs] at heq
    exact Or.inl ⟨z, ⟨hz.1, hzD⟩, by nlinarith [heq]⟩
  · exact Or.inr ⟨z, ⟨hz.1, hzF⟩, ht⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalBandPathPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the actual paid-threshold conclusion yields the local
variation estimate in image-measure form. Only the generic singleton
statement from the independent-level argument is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem local_band_path_image_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ (H θ), z ∈ B \ Flags →
        ¬ (connectedComponentIn (H θ) z).Nontrivial) :
    ENNReal.ofReal (b - a) ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  let : Countable ↥(range γ ∩ Flags) := (hFlags.mono inter_subset_right).to_subtype
  by_cases hab : a < b
  · have hai := hbranch x (hγV ⟨0, γ.source⟩) a ((ha a).mpr rfl)
    have hbi := hbranch y (hγV ⟨1, γ.target⟩) b ((hb b).mpr rfl)
    have hsub : Ioo a b ⊆ Ioc c (c + 1) := by
      intro t ht
      exact ⟨hai.1.trans_lt ht.1, (ht.2.trans hbi.2).le⟩
    have hreal := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_real_interval_of_ae_circle _ hfree c)
    have hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
        t ∈ f '' (range γ ∩ D) ∨ ∃ z : ↥(range γ ∩ Flags),
          (z.val, t) ∈ intervalFiberHull (clusterGraph D f) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hreal] with t ht hgood
      have hti : t ∈ Ico c (c + 1) := ⟨hai.1.trans ht.1.le, ht.2.trans hbi.2⟩
      rcases local_band_paid_values hsard hsch G π hπ hclosed hsurj hr
        hB hTD hbad hBD hdense hD hV hinfty hM hf H hH hlevel γ hγV ha hb ht.1 ht.2 hti
        hbranch hgood with hdom | ⟨z, hz, hzt⟩
      · exact Or.inl hdom
      · exact Or.inr ⟨⟨z, hz⟩, hzt⟩
    exact interval_band_payment_of_ae_cover hM (fun z : ↥(range γ ∩ Flags) => z.val)
      (fun z => by rw [hdense.closure_eq]; trivial) (f '' (range γ ∩ D)) a b hcover
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hab))]
    exact bot_le

theorem local_band_path_abs_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ (H θ), z ∈ B \ Flags →
        ¬ (connectedComponentIn (H θ) z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact local_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel γ hγV ha hb hbranch hfree
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    rw [abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    have hγ' : range γ.symm ⊆ V := by simpa only [Path.symm_range] using hγV
    have hf' : ∀ᵐ θ : UnitAddCircle ∂volume,
        ∀ z ∈ range γ.symm ∩ (H θ), z ∈ B \ Flags →
          ¬ (connectedComponentIn (H θ) z).Nontrivial := by
      simpa only [Path.symm_range] using hfree
    have hp := local_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel γ.symm hγ' hb ha hbranch hf'
    have hset : range γ.symm ∩ Flags = range γ ∩ Flags := by rw [Path.symm_range]
    rw [hset] at hp
    simpa only [Path.symm_range] using hp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalBandIntervalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute variation on an actual parameter interval, paid by domain
image length and the atomic measure of flagged visits. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem local_band_interval_image_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    (γ : C(PathTime, Sphere)) {r s : PathTime} (hrs : r < s)
    (hγV : γ '' Icc r s ⊆ V)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ '' Icc r s ∩ (H θ), z ∈ B \ Flags →
        ¬ (connectedComponentIn (H θ) z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (γ '' Icc r s ∩ D)) + boundaryTimeMeasure γ m (Icc r s) := by
  let α := intervalPath γ r s
  have hrange : range α = γ '' Icc r s := intervalPath_range γ hrs
  have hp := local_band_path_abs_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel α
    (by simpa only [hrange] using hγV) ha hb hbranch
    (by simpa only [hrange] using hfree)
  have hset : range α ∩ Flags = γ '' Icc r s ∩ Flags := by rw [hrange]
  rw [hset, hrange] at hp
  apply hp.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' z : ↥(γ '' Icc r s ∩ Flags), m z.val :=
      ENNReal.tsum_le_tsum (fun z => hm z.val ⟨z.property.2, hγV z.property.1⟩)
    _ ≤ _ := boundaryTimeMeasure_image_le γ m measurableSet_Icc inter_subset_left

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalBandPhysicalPayment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The singleton-contact argument gives a physical payment
inequality on every retained parameter interval. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r5b7c64_5 : BorelSpace Sphere := ⟨rfl⟩
theorem local_band_interval_physical_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {r s : PathTime} (hrs : r < s)
    (hγV : γ.val '' Icc r s ⊆ V)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ γ.val '' Icc r s ∩ D, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ.val r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ.val s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ.val '' Icc r s ∩ (H θ), z ∈ B \ Flags →
        ¬ (connectedComponentIn (H θ) z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ physicalTagPayment e y₀ γ
      (fun y => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y) m (Icc r s) := by
  have hp := local_band_interval_image_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel γ.val hrs hγV m hm ha hb hbranch hfree
  have hi := quotient_smooth_interval_image_le_physical e hU y₀ π hπ he φ hφ hA hφA
    hAG hAO hO j hjm hj L hL γ hrs hv f D hvf hcover
  exact hp.trans (by
    change _ ≤ tagPaymentMeasure (physicalTimeLength e y₀ γ)
      (fun t => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) (physicalValue e y₀ (γ.val t))) γ.val m (Icc r s)
    rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ measurableSet_Icc]
    exact add_le_add hi le_rfl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_LocalBandTagNullTrace
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null free traces inside a tag: the local variation estimate and its
finite physical-plus-visit payment measure are both constructed above. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r5b7c64_6 : BorelSpace Sphere := ⟨rfl⟩
theorem local_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {T : Set PathTime} (hT : IsOpen T)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ range γ.val ∩ D ∩ V, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    (hmFree : ∀ z ∈ B \ Flags, m z = 0) (hBU : B ⊆ Uᶜ)
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (B \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T,
      γ.val t ∈ B \ Flags → γ.val t ∈ H θ →
      ¬ (connectedComponentIn (H θ) (γ.val t)).Nontrivial)
    (hcost : (∫⁻ y, (L : ℝ≥0∞) * (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y ∂dyadicPhysicalOccupation e y₀ γ) +
      boundaryToll γ.val m < ∞) :
    volume ((trace ∘ γ.val) ''
      ((γ.val ⁻¹' (B \ Flags)) ∩ (T ∩ γ.val ⁻¹' V))) = 0 := by
  let g : Sphere → ℝ≥0∞ := fun y => (L : ℝ≥0∞) * (φ '' A).indicator
    (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y
  have hg : Measurable g := measurable_const.mul
    ((((measurable_fderiv ℝ v).norm.ennreal_ofReal).comp hjm).indicator hφA)
  let κ := physicalTagPayment e y₀ γ g m
  let : IsFiniteMeasure κ := physicalTagPayment_finite e hU y₀ γ g hg m hcost
  have hF : MeasurableSet (γ.val ⁻¹' (B \ Flags)) :=
    γ.val.continuous.measurable (hB.measurableSet.diff hFlags.measurableSet)
  have hκF : κ (γ.val ⁻¹' (B \ Flags)) = 0 :=
    physicalTagPayment_null_free e hU y₀ γ g m hF
      (fun t ht => hBU ht.1) (fun t ht => hmFree (γ.val t) ht)
  apply path_time_null_image_of_interval_payment κ
    (hT.inter (hV.preimage γ.val.continuous))
    (measure_mono_null inter_subset_left hκF) (trace ∘ γ.val)
  intro r hr' s hs' hrs hI
  rcases hrs.eq_or_lt with hrs | hrs
  · subst s
    simp only [comp_apply, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hp := local_band_interval_physical_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel e hU y₀ he φ hφ hA hφA
      hAG hAO hO j hjm hj L hL γ hrs
      (by
        rintro x ⟨t, ht, rfl⟩
        exact (hI ht).2)
      hv hvf
      (by
        rintro x ⟨⟨t, ht, rfl⟩, hxD⟩
        exact hcover (γ.val t) ⟨⟨mem_range_self t, hxD⟩, (hI ht).2⟩)
      m hm (htrace (γ.val r) ⟨hr'.1, hr'.2.2⟩)
      (htrace (γ.val s) ⟨hs'.1, hs'.2.2⟩) hbranch ?_
    · exact hp
    · filter_upwards [hgood] with θ hθ
      rintro z ⟨⟨t, ht, htz⟩, hz⟩ hfree
      subst z
      exact hθ t (hI ht).1 hfree hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LawLocalBandTagNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Application of the local tag proof to a physical path law. The
inverse-chart bound and the finite payment measure are constructed from
the quotient neighborhood, the differential energy and the law's density.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_7 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_parameter_local_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {G U V Flags : Set Sphere} (hG : IsOpen G) (hU : IsOpen U) (hdense : Dense U)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (e : G ≃ₜ U) (y₀ : Sphere) (he : ∀ y : G, (e y).val = π y.val)
    (hTD : IsTotallyDisconnected Uᶜ) (hbad : ∀ p ∈ Gᶜ, π p ∈ Uᶜ)
    (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ closure V) (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ U, |f z| ≤ M) (hf : ContinuousOn f (U ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph U f ↔ z ∈ H θ)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) ((((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V)))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, Sphere)) (hγmap : Measurable γmap)
    (μ : ProbabilityMeasure C(PathTime, Sphere)) (hμ : P.map (f := γmap) (by first | exact hγmap.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) = μ)
    (hfinite : ∀ᵐ z ∂(P : Measure Z), physicalDomainLength e y₀ (γmap z) < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞)
    (hband : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[U] z) - liminf f (𝓝[U] z)) ≤ m z)
    (hmFree : ∀ z ∈ Uᶜ \ Flags, m z = 0)
    (T : Z → Set PathTime) (hT : ∀ z, IsOpen (T z))
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (Uᶜ \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph U f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T z,
      γmap z t ∈ Uᶜ \ Flags → γmap z t ∈ H θ →
      ¬ (connectedComponentIn (H θ) (γmap z t)).Nontrivial) :
    ∀ᵐ z ∂(P : Measure Z), volume ((trace ∘ γmap z) ''
      ((γmap z ⁻¹' (Uᶜ \ Flags)) ∩ (T z ∩ γmap z ⁻¹' V))) = 0 := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := O ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖fderiv ℝ v z‖
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hA : MeasurableSet A := (hO.inter (hV.preimage (hπ.comp OnePoint.continuous_coe))).measurableSet
  obtain ⟨L, hL⟩ := finiteCoord_lipschitz_quotient_neighborhood π hπ G V hinfty
  let g := localizedSphericalChartWeight L A k
  have hk : Measurable k := (measurable_fderiv ℝ v).norm.ennreal_ofReal
  have hg : Measurable g := measurable_localizedSphericalChartWeight L hA hk
  have hg2 : (∫⁻ y, g y ^ 2 ∂sphericalArea) < ∞ :=
    localizedSphericalChartWeight_square_finite L hA hk
      henergy
  have hcost := ae_physical_and_visit_cost_finite e hU y₀ μ sphericalArea ρ g hρ hg hocc
    hρ2 hg2 m hm hweight hvisits
  have hcostZ : ∀ᵐ z ∂(P : Measure Z),
      (∫⁻ y, g y ∂physicalOccupationCode e y₀ (γmap z)) + boundaryToll (γmap z) m < ∞ := by
    have hmap : (P : Measure Z).map γmap = (μ : Measure C(PathTime, Sphere)) := by
      rw [← ProbabilityMeasure.toMeasure_map P hγmap.aemeasurable, hμ]
    exact ae_of_ae_map hγmap.aemeasurable (hmap.symm ▸ hcost)
  filter_upwards [hfinite, hcostZ, hgood] with z hγ hc hγgood
  let γp : FinitePhysicalPath e y₀ := ⟨γmap z, hγ⟩
  rw [physicalOccupationCode_eq e y₀ γp] at hc
  exact local_band_tag_null_trace (B := Uᶜ) (D := U) hsard hsch G π hπ hclosed hsurj hr
    hU.isClosed_compl hTD hbad (by simpa only [compl_compl] using (Subset.rfl : U ⊆ U)) hdense hU hV
    (fun h => hinfty (subset_closure h)) hFlags hM hf H hH hlevel e hU y₀ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA
    (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hA)
    (fun _ hz => hz.1) (Subset.rfl : A ⊆ A)
    (hO.inter (hV.preimage (hπ.comp OnePoint.continuous_coe))) finiteCoord measurable_finiteCoord
    (fun z _ => finiteCoord_coe z) L hL γp (hT z) hv (fun _ _ => rfl)
    (fun x hx => quotient_neighborhood_chart_covers e π he
      (fun h => hinfty (subset_closure h)) x ⟨hx.1.2, hx.2⟩)
    m hband hmFree (fun _ hx => hx) trace htrace hbranch hγgood hc

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalBandIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local real trace estimates remove circle-level incidences. Their
assembly uses outer measure only, so the free set need not be Borel. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

theorem local_level_incidence_null_of_real_trace
    {X : Type*} [TopologicalSpace X]
    (D Free V : Set X) (H : Set (UnitAddCircle × X))
    (f trace : X → ℝ) (γ : C(PathTime, X)) (T : Set PathTime)
    (hlevel : ∀ x ∈ V, ∀ θ, (x, θ) ∈ circleBandGraph D f ↔ (θ, x) ∈ H)
    (htrace : ∀ x ∈ Free ∩ V, ∀ a,
      (x, a) ∈ intervalFiberHull (clusterGraph D f) ↔ a = trace x)
    (hnull : volume ((trace ∘ γ) '' (γ ⁻¹' Free ∩ (T ∩ γ ⁻¹' V))) = 0) :
    volume {θ | ∃ t ∈ T, γ t ∈ Free ∩ V ∧ (θ, γ t) ∈ H} = 0 := by
  apply measure_mono_null (t := ((↑) : ℝ → UnitAddCircle) ''
    ((trace ∘ γ) '' (γ ⁻¹' Free ∩ (T ∩ γ ⁻¹' V)))) _
    (volume_addCircle_image_eq_zero hnull)
  rintro θ ⟨t, ht, hx, hθ⟩
  obtain ⟨⟨x, a⟩, ha, he⟩ := (hlevel (γ t) hx.2 θ).mpr hθ
  change (x, (a : UnitAddCircle)) = (γ t, θ) at he
  have hxEq : x = γ t := congrArg Prod.fst he
  subst x
  have haEq : a = trace (γ t) := (htrace (γ t) hx a).mp ha
  refine ⟨trace (γ t), ⟨t, ⟨hx.1, ht, hx.2⟩, rfl⟩, ?_⟩
  simpa only [haEq] using congrArg Prod.snd he

theorem level_incidence_null_of_countable_cover
    {X I : Type*} [TopologicalSpace X] [Countable I]
    (Free : Set X) (H : Set (UnitAddCircle × X))
    (V : I → Set X) (γ : C(PathTime, X)) (T : Set PathTime)
    (hcover : ∀ x ∈ Free, ∀ θ, (θ, x) ∈ H → ∃ i, x ∈ V i)
    (hnull : ∀ i, volume {θ | ∃ t ∈ T, γ t ∈ Free ∩ V i ∧ (θ, γ t) ∈ H} = 0) :
    volume {θ | ∃ t ∈ T, γ t ∈ Free ∧ (θ, γ t) ∈ H} = 0 := by
  apply measure_mono_null (t := ⋃ i : I,
    {θ | ∃ t ∈ T, γ t ∈ Free ∩ V i ∧ (θ, γ t) ∈ H}) _ (measure_iUnion_null hnull)
  rintro θ ⟨t, ht, hx, hθ⟩
  obtain ⟨i, hi⟩ := hcover (γ t) hx θ hθ
  exact mem_iUnion.mpr ⟨i, t, ht, ⟨hx, hi⟩, hθ⟩

attribute [local instance] sphereMetric sphereBorel

local instance localInst_r5b7c64_8 : BorelSpace Sphere := ⟨rfl⟩
theorem ae_code_free_incidence_null_of_local_real_traces
    [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
    (d : PathCodeData Sphere Sphere) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set Sphere) (hFree : Free ⊆ d.dust)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set Sphere))
    {I : Type*} [Countable I] (V : I → Set Sphere) (f trace : I → Sphere → ℝ)
    (hcover : ∀ x ∈ Free, ∀ θ, (θ, x) ∈ d.levels i → ∃ j, x ∈ V j)
    (hlevel : ∀ j x, x ∈ V j → ∀ θ,
      (x, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, x) ∈ d.levels i)
    (htrace : ∀ j x, x ∈ Free ∩ V j → ∀ a,
      (x, a) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ a = trace j x)
    (hnull : ∀ j, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume ((trace j ∘ Γ.val.1) '' (Γ.val.1 ⁻¹' Free ∩
        (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V j))) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ Free, (θ, x) ∈ d.levels i} = 0 := by
  apply ae_code_free_level_incidence_null_of_tags d P i Free hFree hm hweight hvisits hdeleteCover hdelete
  filter_upwards [ae_all_iff.mpr hnull] with Γ hΓ
  intro k
  apply level_incidence_null_of_countable_cover Free (d.levels i) V Γ.val.1
    (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k))) hcover
  intro j
  exact local_level_incidence_null_of_real_trace d.quotientDomain Free (V j)
    (d.levels i) (f j) (trace j) Γ.val.1 _ (hlevel j) (htrace j) (hΓ j k)

end CircleDomainRigidity

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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemForallFinRealPathTimeSeparatedTimes _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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

theorem later_ray_right (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {k l : ℤ} (hkl : k < l) (H : ℂ ≃ₜ ℂ)
    (hH : (translatedHalfPlaneRay γ hγ k).IsJordan H) (t : DiskRayTime) :
    halfPlaneDisk ((translatedHalfPlaneRay γ hγ l).curve t) ∉ closure (jordanInterior H) := by
  have h := translated_ray_side_value γ hγ hkl.ne H hH t
  rw [ite_eq_right (not_le_of_gt hkl)] at h
  intro hi
  rw [ite_eq_left hi] at h
  cases h

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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_RayFamilyMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
-- module Solutions.Q146_CD.CircleDomains_Probability_GeometricIndexMeasurable
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RayIndexOscillation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near an interior point, a simple lifted ray has index jump at most
one. The jump is zero when the projected point misses the arc. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem geometricRayIndex_on_translated_ray
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet) (k : ℤ) (t : DiskRayTime) :
    geometricRayIndex hsch γ hγ ((translatedHalfPlaneRay γ hγ k).curve t) = k - 1 := by
  let z := (translatedHalfPlaneRay γ hγ k).curve t
  have hz : 0 ≤ z.im := (translatedHalfPlaneRay γ hγ k).nonneg t
  have hlo : k - 1 ≤ geometricRayIndex hsch γ hγ z := by
    apply (mem_rayRightIndices_iff_le hsch hsep γ hγ z hz (k - 1)).mp
    exact later_ray_right γ hγ (by omega) _ (rayJordan_spec hsch γ hγ (k - 1)) t
  have hnot : k ∉ rayRightIndices hsch γ hγ z := by
    intro hk
    apply hk
    apply frontier_subset_closure
    rw [rayJordan_spec hsch γ hγ k]
    left
    exact ⟨t.val, by
      change (translatedHalfPlaneRay γ hγ k).compactify t.val = halfPlaneDisk z
      rw [HalfPlaneRay.compactify, dite_eq_left t.property]⟩
  have hhi : ¬ k ≤ geometricRayIndex hsch γ hγ z :=
    fun hk => hnot ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz k).mpr hk)
  change geometricRayIndex hsch γ hγ z = k - 1
  omega

 theorem rayInterior_of_index_lt_of_avoids
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    {z : ℂ} (hz : 0 < z.im) (k : ℤ) (hk : geometricRayIndex hsch γ hγ z < k)
    (hmiss : halfPlaneDisk z ∉ range (translatedHalfPlaneRay γ hγ k).crosscut) :
    halfPlaneDisk z ∈ jordanInterior (rayJordan hsch γ hγ k) := by
  have hcl : halfPlaneDisk z ∈ closure (jordanInterior (rayJordan hsch γ hγ k)) := by
    by_contra hn
    exact (not_le_of_gt hk)
      ((mem_rayRightIndices_iff_le hsch hsep γ hγ z hz.le k).mp hn)
  by_contra hi
  have hfront : halfPlaneDisk z ∈ frontier (jordanInterior (rayJordan hsch γ hγ k)) := by
    rw [(jordanInterior_isOpen _).frontier_eq]
    exact ⟨hcl, hi⟩
  rw [rayJordan_spec hsch γ hγ k] at hfront
  rcases hfront with hc | ⟨t, ht⟩
  · exact hmiss hc
  · have hn := halfPlaneDisk_norm_lt hz
    rw [← ht, boundaryClosingArc_norm] at hn
    exact lt_irrefl _ hn

 theorem eventually_geometricRayIndex_bounds
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      geometricRayIndex hsch γ hγ z.val ≤ geometricRayIndex hsch γ hγ w.val ∧
      geometricRayIndex hsch γ hγ w.val ≤ geometricRayIndex hsch γ hγ z.val +
        if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  let n := geometricRayIndex hsch γ hγ z.val
  let k := n + if diskRayProjection z.val ∈ range γ then 2 else 1
  have hnk : n < k := by dsimp [k]; split_ifs <;> omega
  have hmiss : halfPlaneDisk z.val ∉ range (translatedHalfPlaneRay γ hγ k).crosscut := by
    intro hh
    obtain ⟨t, ht⟩ := ((translatedHalfPlaneRay γ hγ k).cayley_mem_crosscut_iff z.property).mp hh
    have hidx := geometricRayIndex_on_translated_ray hsch hsep γ hγ k t
    rw [ht] at hidx
    have hhit : diskRayProjection z.val ∈ range γ := by
      refine ⟨t.val, ?_⟩
      rw [← diskRayProjection_translated γ hγ k t, ht]
    dsimp [k] at hidx
    rw [ite_eq_left hhit] at hidx
    dsimp [n] at hidx
    omega
  have hleft := rayInterior_of_index_lt_of_avoids hsch hsep γ hγ hz k hnk hmiss
  have hright : halfPlaneDisk z.val ∉ closure (jordanInterior (rayJordan hsch γ hγ n)) :=
    (geometricRayIndex_isGreatest hsch γ hγ z.val z.property).1
  have hD : Continuous (fun w : ClosedUpperHalfPlane => halfPlaneDisk w.val) :=
    continuousOn_halfPlaneDisk.comp_continuous continuous_subtype_val (fun w => w.property)
  have hnearlo := hD.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hright)
  have hnearhi := hD.continuousAt.eventually ((jordanInterior_isOpen _).mem_nhds hleft)
  filter_upwards [hnearlo, hnearhi] with w hwlo hwhi
  refine ⟨(mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property n).mp hwlo, ?_⟩
  have hlt : geometricRayIndex hsch γ hγ w.val < k := by
    by_contra hn
    have hm := (mem_rayRightIndices_iff_le hsch hsep γ hγ w.val w.property k).mpr
      (le_of_not_gt hn)
    exact hm (subset_closure hwhi)
  dsimp [k] at hlt
  dsimp [n] at *
  split_ifs at * <;> omega

 theorem eventually_geometricRayIndex_pair_difference
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (γ : C(PathTime, ℂ)) (hγ : γ ∈ diskTerminalArcSet)
    (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |(geometricRayIndex hsch γ hγ p.1.val : ℝ) -
        (geometricRayIndex hsch γ hγ p.2.val : ℝ)| ≤
          if diskRayProjection z.val ∈ range γ then 1 else 0 := by
  have hb := eventually_geometricRayIndex_bounds hsch hsep γ hγ z hz
  have h₁ := (continuous_fst.tendsto (z, z)).eventually hb
  have h₂ := (continuous_snd.tendsto (z, z)).eventually hb
  filter_upwards [h₁, h₂] with p hp hq
  split_ifs at * with hhit
  · apply abs_le.mpr
    constructor
    · have h : -(1 : ℤ) ≤ geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val := by omega
      exact_mod_cast h
    · have h : geometricRayIndex hsch γ hγ p.1.val - geometricRayIndex hsch γ hγ p.2.val ≤ (1 : ℤ) := by omega
      exact_mod_cast h
  · have he : geometricRayIndex hsch γ hγ p.1.val =
        geometricRayIndex hsch γ hγ p.2.val := by omega
    simp only [he, sub_self, abs_zero, le_refl]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanIndexOscillation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local oscillation of the averaged index is bounded by the
probability that the sampled arc hits the projected point. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem meanGeometricIndex_oscillation_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (z : ClosedUpperHalfPlane) (hz : 0 < z.val.im)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| <
        (η : Measure K).real {γ | diskRayProjection z.val ∈ range γ.val} + ε := by
  classical
  let H : Set K := {γ | diskRayProjection z.val ∈ range γ.val}
  have hH : MeasurableSet H := (isClosed_paths_hitting (diskRayProjection z.val)).measurableSet.preimage
    measurable_subtype_coe
  let I : K → ℝ := H.indicator 1
  let n : ClosedUpperHalfPlane → K → ℝ := fun w γ =>
    geometricRayIndex hsch γ.val (hKS γ.property) w.val
  let E : ClosedUpperHalfPlane × ClosedUpperHalfPlane → K → ℝ := fun p γ =>
    max (|n p.1 γ - n p.2 γ| - I γ) 0
  have hI : Integrable I (η : Measure K) := (integrable_const 1).indicator hH
  have hInon (γ : K) : 0 ≤ I γ := by by_cases h : γ ∈ H <;> simp [I, h]
  have hn (w : ClosedUpperHalfPlane) : Integrable (n w) (η : Measure K) :=
    integrable_geometricRayIndex hsch hsep K hK hKS η w
  have hE (p : ClosedUpperHalfPlane × ClosedUpperHalfPlane) : Integrable (E p) (η : Measure K) :=
    (((hn p.1).sub (hn p.2)).abs.sub hI).sup (integrable_const 0)
  have hlim : ∀ᵐ γ : K ∂(η : Measure K),
      Tendsto (fun p => E p γ) (𝓝 (z, z)) (𝓝 0) := by
    apply Eventually.of_forall
    intro γ
    have hb := eventually_geometricRayIndex_pair_difference hsch hsep γ.val (hKS γ.property) z hz
    have he : ∀ᶠ p in 𝓝 (z, z), E p γ = 0 := by
      filter_upwards [hb] with p hp
      dsimp [E, n]
      apply max_eq_right
      have hi : I γ = if diskRayProjection z.val ∈ range γ.val then 1 else 0 := by
        rfl
      rw [hi]
      linarith
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  let X := |z.val.re| + 1
  let Y := z.val.im + 1
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hY : 0 ≤ Y := by dsimp [Y] <;> linarith
  obtain ⟨M, hM⟩ := compact_geometricRayIndex_bound hsch K hK hKS X Y hX hY
  have hnear : ∀ᶠ w : ClosedUpperHalfPlane in 𝓝 z,
      |w.val.re| ≤ X ∧ w.val.im ≤ Y := by
    have h₁ := ((Complex.continuous_re.comp continuous_subtype_val).abs.continuousAt
      (x := z)).eventually (isOpen_Iio.mem_nhds (show |z.val.re| < X by dsimp [X]; linarith))
    have h₂ := (Complex.continuous_im.comp continuous_subtype_val).continuousAt
      (x := z) |>.eventually (isOpen_Iio.mem_nhds (show z.val.im < Y by dsimp [Y] <;> linarith))
    filter_upwards [h₁, h₂] with w hw₁ hw₂
    exact ⟨hw₁.le, hw₂.le⟩
  have hbound : ∀ᶠ p : ClosedUpperHalfPlane × ClosedUpperHalfPlane in 𝓝 (z, z),
      ∀ᵐ γ : K ∂(η : Measure K), ‖E p γ‖ ≤ 2 * |M| := by
    filter_upwards [(continuous_fst.tendsto (z, z)).eventually hnear,
      (continuous_snd.tendsto (z, z)).eventually hnear] with p hp hq
    apply Eventually.of_forall
    intro γ
    have h₁ : |n p.1 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.1.val.re p.1.val.im hp.1 p.1.property hp.2
    have h₂ : |n p.2 γ| ≤ M := by
      simpa only [n, Complex.re_add_im] using hM γ p.2.val.re p.2.val.im hq.1 p.2.property hq.2
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have ht := abs_sub (n p.1 γ) (n p.2 γ)
      linarith [hInon γ, le_abs_self M]
    · positivity
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun _ : K => 2 * |M|)
    (Eventually.of_forall fun p => (hE p).aestronglyMeasurable) hbound
    (integrable_const _) hlim
  have hconv' : Tendsto (fun p => ∫ γ, E p γ ∂(η : Measure K)) (𝓝 (z, z)) (𝓝 0) := by
    simpa only [integral_zero] using hconv
  have hevent : ∀ᶠ p in 𝓝 (z, z), (∫ γ, E p γ ∂(η : Measure K)) < ε :=
    hconv'.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hevent] with p hp
  have hcomp : |meanGeometricIndex hsch K hKS η p.1 - meanGeometricIndex hsch K hKS η p.2| ≤
      (∫ γ, I γ ∂(η : Measure K)) + ∫ γ, E p γ ∂(η : Measure K) := by
    change |(∫ γ, n p.1 γ ∂(η : Measure K)) - (∫ γ, n p.2 γ ∂(η : Measure K))| ≤ _
    rw [← integral_sub (hn p.1) (hn p.2), ← integral_add hI (hE p)]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono ((hn p.1).sub (hn p.2)).abs (hI.add (hE p))
    intro γ
    dsimp [E]
    linarith [le_max_left (|n p.1 γ - n p.2 γ| - I γ) 0]
  have hmass : (∫ γ, I γ ∂(η : Measure K)) = (η : Measure K).real H :=
    integral_indicator_one hH
  rw [hmass] at hcomp
  change _ < (η : Measure K).real H + ε
  linarith

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

theorem periodBandGraph_singular {ι : Type*}
    (D M : Set Sphere) (b : Sphere) (V : ι → Set Sphere) (f : ι → Sphere → ℝ)
    (hb : b ∈ M) (θ : UnitAddCircle) : (b, θ) ∈ periodBandGraph D M b V f :=
  ⟨hb, Or.inl rfl⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanIndexBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary band widths of the actual mean are bounded by point hit
probabilities. This applies after any continuous local lift, including
limits along the physical domain at a collapsed complementary component. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem limsup_sub_liminf_le_of_pair_oscillation
    {X : Type*} (l : Filter X) [NeBot l] (u : X → ℝ) (C : ℝ)
    (hlo : IsBoundedUnder (· ≥ ·) l u) (hhi : IsBoundedUnder (· ≤ ·) l u)
    (hpair : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : X × X in l ×ˢ l, |u p.1 - u p.2| < C + ε) :
    limsup u l - liminf u l ≤ C := by
  by_contra hn
  let ε := (limsup u l - liminf u l - C) / 2
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp (hpair ε hε)
  have he : ∀ᶠ y in l, limsup u l - C - ε ≤ u y := by
    filter_upwards [hQ] with y hy
    have hb : limsup u l ≤ u y + C + ε := by
      apply limsup_le_of_le hlo.isCoboundedUnder_le
      filter_upwards [hP] with x hx
      have hh := hPQ hx hy
      have ha := le_abs_self (u x - u y)
      linarith
    linarith
  have hl := le_liminf_of_le hhi.isCoboundedUnder_ge he
  dsimp [ε] at hl
  linarith

 theorem meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    {X : Type*} [TopologicalSpace X] (S : Set X) (s : X) (hs : s ∈ closure S)
    (L : X → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) :
    limsup (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) -
      liminf (fun x => meanGeometricIndex hsch K hKS η (L x)) (𝓝[S] s) ≤
        (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : X → ℝ := fun x => meanGeometricIndex hsch K hKS η (L x)
  let C := (η : Measure K).real {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz zero_lt_one
  have hnear : ∀ᶠ x in 𝓝[S] s, |u x - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).1
      exact (show u s - C - 1 ≤ u x by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun x hx => by
      have hh := (abs_lt.mp hx).2
      exact (show u x ≤ u s + C + 1 by linarith))
  apply limsup_sub_liminf_le_of_pair_oscillation (𝓝[S] s) u C hlo hhi
  intro ε hε
  have hmap := Filter.Tendsto.prodMap
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
    (show Tendsto L (𝓝[S] s) (𝓝 (L s)) from hL)
  rw [← nhds_prod_eq] at hmap
  exact hmap.eventually (meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS η (L s) hz hε)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_MappedMeanBands
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mean-index band bound in the original path law. Injectivity of
the actual Jordan coordinate identifies the hit event exactly. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)]

 theorem mapped_arc_hit_probability_eq
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ)) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x})) :
    ((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K).real {γ | F x ∈ range γ.val} =
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hH : MeasurableSet {γ : K | F x ∈ range γ.val} :=
    (isClosed_paths_hitting (F x)).measurableSet.preimage measurable_subtype_coe
  have he : f ⁻¹' {γ : K | F x ∈ range γ.val} = {γ : A | x ∈ range γ.val} := by
    ext γ
    change F x ∈ range (f γ).val ↔ x ∈ range γ.val
    rw [hmap γ]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, hF γ (Or.inl (mem_range_self t)) (Or.inr (mem_singleton x)) ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, congrArg F ht⟩
  rw [measureReal_def, ProbabilityMeasure.toMeasure_map, Measure.map_apply hf hH, he,
    measureReal_def]

 theorem mapped_meanGeometricIndex_band_width
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x) :
    limsup (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s) -
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s) ≤
        (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hb := meanGeometricIndex_band_width hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) S s hs L hL hz
  rw [hproj, mapped_arc_hit_probability_eq A K η F f hf hmap x hF] at hb
  exact hb

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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CircleSmoothingBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing discrepancy tending to zero leaves both endpoints of
every bounded local real band unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem bounded_bands_eq_of_sub_tendsto_zero
    {X : Type*} {l : Filter X} [NeBot l] {u v : X → ℝ}
    (hul : IsBoundedUnder (· ≥ ·) l u) (huu : IsBoundedUnder (· ≤ ·) l u)
    (hsub : Tendsto (fun x => v x - u x) l (𝓝 0)) :
    liminf v l = liminf u l ∧ limsup v l = limsup u l := by
  let r := fun x => v x - u x
  have heq : u + r = v := by
    funext x
    dsimp [r]
    ring
  have heq' : r + u = v := by rw [add_comm, heq]
  have hrl : IsBoundedUnder (· ≥ ·) l r := hsub.isBoundedUnder_ge
  have hru : IsBoundedUnder (· ≤ ·) l r := hsub.isBoundedUnder_le
  have hlo := le_liminf_add (u := u) (v := r) hul huu hrl hru.isCoboundedUnder_ge
  have hhi := liminf_add_le (u := r) (v := u) hrl hru hul huu.isCoboundedUnder_ge
  have hsuplo := le_limsup_add (u := u) (v := r) huu hul.isCoboundedUnder_le hru hrl
  have hsuphi := limsup_add_le (u := u) (v := r) hul huu hrl.isCoboundedUnder_le hru
  have hliminf : liminf r l = 0 := hsub.liminf_eq
  have hlimsup : limsup r l = 0 := hsub.limsup_eq
  rw [heq, hliminf, add_zero] at hlo hsuplo
  rw [heq', hlimsup, zero_add] at hhi
  rw [heq, hlimsup, add_zero] at hsuphi
  exact ⟨le_antisymm hhi hlo, le_antisymm hsuphi hsuplo⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PerturbedMeanBands
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smoothed stream has the same dust bands as the actual mean when
its real correction vanishes there. The width remains the original
point-hit probability. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

theorem perturbed_mapped_mean_bands
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, X)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(X, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (x : X) (hF : ∀ γ : A, InjOn F (range γ.val ∪ {x}))
    {Y : Type*} [TopologicalSpace Y] (S : Set Y) (s : Y) (hs : s ∈ closure S)
    (L : Y → ClosedUpperHalfPlane) (hL : ContinuousWithinAt L S s)
    (hz : 0 < (L s).val.im) (hproj : diskRayProjection (L s).val = F x)
    (v : Y → ℝ)
    (herr : Tendsto (fun y => v y - meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y))
      (𝓝[S] s) (𝓝 0)) :
    (liminf v (𝓝[S] s) =
      liminf (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s)) ∧
    (limsup v (𝓝[S] s) =
      limsup (fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)) (𝓝[S] s)) ∧
    limsup v (𝓝[S] s) - liminf v (𝓝[S] s) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  let : NeBot (𝓝[S] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  let u : Y → ℝ := fun y => meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L y)
  let C := ((η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) : ProbabilityMeasure K) : Measure K).real
    {γ | diskRayProjection (L s).val ∈ range γ.val}
  have hbase := meanGeometricIndex_oscillation_le_hit hsch hsep K hK hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
    (L s) hz zero_lt_one
  have hnear : ∀ᶠ y in 𝓝[S] s, |u y - u s| < C + 1 :=
    (hL.prodMk_nhds tendsto_const_nhds).eventually hbase
  have hlo : IsBoundedUnder (· ≥ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_ge (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).1
      exact (show u s - C - 1 ≤ u y by linarith))
  have hhi : IsBoundedUnder (· ≤ ·) (𝓝[S] s) u :=
    isBoundedUnder_of_eventually_le (hnear.mono fun y hy => by
      have hh := (abs_lt.mp hy).2
      exact (show u y ≤ u s + C + 1 by linarith))
  have heq := bounded_bands_eq_of_sub_tendsto_zero hlo hhi herr
  refine ⟨heq.1, heq.2, ?_⟩
  rw [heq.1, heq.2]
  exact mapped_meanGeometricIndex_band_width hsch hsep A K hK hKS η F f hf hmap
    x hF S s hs L hL hz hproj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LogarithmicCutCharts
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
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

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MeanPeriodBudget
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed mean-period graph is paid for by the selected
law's point-hit probabilities, with unit budget at its terminal point. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
theorem logarithmicCutChart_im_pos (a : ℝ) {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < 1) :
    0 < (logarithmicCutChart a z).im := by
  have hlog := Real.log_neg (norm_pos_iff.mpr h0) h1
  simpa only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add] using neg_pos.mpr hlog

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteLevelAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

theorem pathImageCount_mono_target {A B : Set X} (hAB : A ⊆ B) (γ : C(PathTime, X)) :
    pathImageCount A γ ≤ pathImageCount B γ := by
  unfold pathImageCount
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ range γ ∩ A
  · simp only [hx, show x ∈ range γ ∩ B from ⟨hx.1, hAB hx.2⟩, ite_true, if_true, le_refl]
  · simp only [hx, ite_false, if_false, zero_le]

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
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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
-- module Solutions.Q146_CD.CircleDomains_Selection_FlagIntersectionCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceRectifiablePathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
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

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem mean_flag_intersection_count_le
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (a : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ a x)
    (μ : ProbabilityMeasure C(PathTime, X)) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ
      ∂(μ : Measure _)) ≤ ∑' x : S, a x.val * pathHitProbability μ x.val := by
  classical
  let : Countable S := hS.to_subtype
  have hlevel (x : S) : MeasurableSet {t : UnitAddCircle | (t, x.val) ∈ H} :=
    (hH.preimage (continuous_id.prodMk continuous_const)).measurableSet
  have hhit (x : S) : MeasurableSet {γ : C(PathTime, X) | x.val ∈ range γ} :=
    (isClosed_paths_hitting x.val).measurableSet
  have hi (t : UnitAddCircle) :
      (∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ ∂(μ : Measure _)) =
        ∑' x : S, (if (t, x.val) ∈ H then (1 : ℝ≥0∞) else 0) * pathHitProbability μ x.val := by
    simp_rw [pathImageCount_inter_eq_tsum]
    have hprod (x : S) (γ : C(PathTime, X)) :
        (if x.val ∈ range γ ∩ {x | (t, x) ∈ H} then (1 : ℝ≥0∞) else 0) =
        (if (t, x.val) ∈ H then (1 : ℝ≥0∞) else 0) * (if x.val ∈ range γ then 1 else 0) := by
      by_cases hl : (t, x.val) ∈ H <;> by_cases hh : x.val ∈ range γ <;> simp [hl, hh]
    simp_rw [hprod]
    rw [lintegral_tsum]
    · apply tsum_congr
      intro x
      rw [lintegral_const_mul]
      · congr 1
        change (∫⁻ γ, Set.indicator {γ : C(PathTime, X) | x.val ∈ range γ} 1 γ
          ∂(μ : Measure C(PathTime, X))) =
          (μ : Measure C(PathTime, X)) {γ : C(PathTime, X) | x.val ∈ range γ}
        exact lintegral_indicator_one (hhit x)
      · exact (measurable_one.indicator (hhit x))
    · intro x
      exact (measurable_const.mul (measurable_one.indicator (hhit x))).aemeasurable
  simp_rw [hi]
  rw [lintegral_tsum]
  · apply ENNReal.tsum_le_tsum
    intro x
    change (∫⁻ t, {t : UnitAddCircle | (t, x.val) ∈ H}.indicator 1 t *
      pathHitProbability μ x.val) ≤ _
    rw [lintegral_mul_const _ (measurable_one.indicator (hlevel x)), lintegral_indicator_one (hlevel x)]
    exact mul_le_mul' (hband x.val x.property) le_rfl
  · intro x
    exact ((measurable_one.indicator (hlevel x)).mul measurable_const).aemeasurable

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

theorem tsum_flag_weight_hit_finite
    (S : Set X) (m : X → ℝ≥0∞) (μ : ProbabilityMeasure C(PathTime, X))
    (hm : (support m).Countable)
    (ha : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    (∑' x : S, m x.val * pathHitProbability μ x.val) < ∞ := by
  let : Countable (support m) := hm.to_subtype
  have hs : (∑' x : X, m x * pathHitProbability μ x) =
      ∑' x : support m, m x.val * pathHitProbability μ x.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun x : X => m x * pathHitProbability μ x)
    intro x hx
    by_contra hn
    have hz : m x = 0 := notMem_support.mp hn
    simp only [mem_support, hz, zero_mul, ne_eq, not_true_eq_false] at hx
  calc
    _ ≤ ∑' x : X, m x * pathHitProbability μ x :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = _ := hs
    _ ≤ countingSquareNorm (fun x : support m => m x.val) *
        countingSquareNorm (fun x : support m => pathHitProbability μ x.val) :=
      tsum_mul_le_countingSquareNorm _ _
    _ ≤ countingSquareNorm (fun x : support m => m x.val) *
        countingSquareNorm (fun x : support m => meanVisitCount μ x.val) :=
      mul_le_mul' le_rfl (countingSquareNorm_mono fun x => pathHitProbability_le_meanVisitCount μ x.val)
    _ < ∞ := ENNReal.mul_lt_top ha hvisits

theorem mean_flag_intersection_count_finite_of_support
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (m : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ m x)
    (μ : ProbabilityMeasure C(PathTime, X))
    (hm : (support m).Countable)
    (ha : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ
      ∂(μ : Measure _)) < ∞ :=
  (mean_flag_intersection_count_le hH S hS m hband μ).trans_lt
    (tsum_flag_weight_hit_finite S m μ hm ha hvisits)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountableClosedLevelCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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

theorem measurable_sigmaCompact_chart_circle_count
    (π : ℂ → X) (hπ : Continuous π) {A : Set ℂ} (hA : IsSigmaCompact A)
    (f : ℂ → ℝ) (hf : ContinuousOn f A) :
    Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (π '' (A ∩ {z | (f z : UnitAddCircle) = p.2})) p.1) := by
  obtain ⟨K, hK, hcover⟩ := hA
  let H : ℕ → Set (X × UnitAddCircle) := fun n =>
    (fun z => (π z, (f z : UnitAddCircle))) '' K n
  have hKA (n : ℕ) : K n ⊆ A := hcover ▸ subset_iUnion K n
  have hH (n : ℕ) : IsClosed (H n) :=
    ((hK n).image_of_continuousOn (hπ.continuousOn.prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn (hf.mono (hKA n))))).isClosed
  have hs (t : UnitAddCircle) : {x | ∃ n, (x, t) ∈ H n} =
      π '' (A ∩ {z | (f z : UnitAddCircle) = t}) := by
    ext x
    constructor
    · rintro ⟨n, z, hz, heq⟩
      exact ⟨z, ⟨hKA n hz, (Prod.mk.inj heq).2⟩, (Prod.mk.inj heq).1⟩
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hz)
      exact ⟨n, z, hn, Prod.ext rfl hzt⟩
  simpa only [hs] using measurable_countable_closed_relation_path_count hH

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
-- module Solutions.Q146_CD.CircleDomains_Selection_MeanLevelAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable distinct-count inequalities let us interchange the path
and level parameters without a separate measurability assumption for
the free-incidence event.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem mean_parameter_level_count_le_of_no_free_hits
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    {Z : Type*} [MeasurableSpace Z] (μ : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hfree : ∀ᵐ z ∂(μ : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H) :
    (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(μ : Measure Z)) ≤
      (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) +
      (∫⁻ t : UnitAddCircle, ∫⁻ z, pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  have hfullZ := hfull.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hdomZ := hdom.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hflagZ := hflag.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hbound : ∀ᵐ z ∂(μ : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) := by
    filter_upwards [hfree] with z hz
    filter_upwards [hz] with t ht
    exact pathImageCount_level_le_of_no_free_hits U Flags _ (γmap z) ht
  have hmeas : MeasurableSet {p : Z × UnitAddCircle |
      pathImageCount {x | (p.2, x) ∈ H} (γmap p.1) ≤
        pathImageCount (U ∩ {x | (p.2, x) ∈ H}) (γmap p.1) +
        pathImageCount (Flags ∩ {x | (p.2, x) ∈ H}) (γmap p.1)} :=
    measurableSet_le hfullZ (hdomZ.add hflagZ)
  have hswap := (Measure.ae_ae_comm hmeas).mp hbound
  have hmeanD : Measurable (fun t : UnitAddCircle => ∫⁻ z,
      pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) ∂(μ : Measure Z)) :=
    (hdomZ.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure Z))
  rw [← lintegral_add_left hmeanD]
  apply lintegral_mono_ae
  filter_upwards [hswap] with t ht
  have hsection : Measurable (fun z : Z => pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z)) :=
    hdomZ.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_mono_ae ht).trans_eq
    (lintegral_add_left hsection (fun z => pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_LevelLawQuantifiers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite expected counts make the free-avoidance statement available
with the independent level chosen first. This uses Borel count inequalities
and does not assume measurability of the raw free-incidence event.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_level_parameter_free_avoidance
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (U Flags : Set X) (hU : IsSigmaCompact U) (hFlags : Flags.Countable)
    (hdisj : Disjoint U Flags)
    {Z : Type*} [MeasurableSpace Z] (P : ProbabilityMeasure Z)
    (γmap : Z → C(PathTime, X)) (hγmap : Measurable γmap)
    (hfree : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H)
    (hmean : (∫⁻ t : UnitAddCircle, ∫⁻ z,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞) :
    ∀ᵐ t : UnitAddCircle ∂volume,
      (∫⁻ z, pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) < ∞ ∧
      ∀ᵐ z ∂(P : Measure Z), ¬ ∃ x ∈ range (γmap z) ∩ (Uᶜ \ Flags), (t, x) ∈ H := by
  have hfull : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount {x | (p.2, x) ∈ H} p.1) := by
    simpa only [exists_const, Prod.swap_prod_mk, mem_preimage] using
      (measurable_countable_closed_relation_path_count
        (H := fun _ : ℕ => Prod.swap ⁻¹' H) (fun _ => hH.preimage continuous_swap))
  have hdom : Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (U ∩ {x | (p.2, x) ∈ H}) p.1) :=
    measurable_sigmaCompact_restricted_relation_path_count hU (hH.preimage continuous_swap)
  have hflag := measurable_flag_intersection_count hH Flags hFlags
  have hfullZ := hfull.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hdomZ := hdom.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hflagZ := hflag.comp (hγmap.prodMap (measurable_id (α := UnitAddCircle)))
  have hbound : ∀ᵐ z ∂(P : Measure Z), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ≤
        pathImageCount (U ∩ {x | (t, x) ∈ H}) (γmap z) +
        pathImageCount (Flags ∩ {x | (t, x) ∈ H}) (γmap z) := by
    filter_upwards [hfree] with z hz
    filter_upwards [hz] with t ht
    exact pathImageCount_level_le_of_no_free_hits U Flags _ (γmap z) ht
  have hmeas : MeasurableSet {p : Z × UnitAddCircle |
      pathImageCount {x | (p.2, x) ∈ H} (γmap p.1) ≤
        pathImageCount (U ∩ {x | (p.2, x) ∈ H}) (γmap p.1) +
        pathImageCount (Flags ∩ {x | (p.2, x) ∈ H}) (γmap p.1)} :=
    measurableSet_le hfullZ (hdomZ.add hflagZ)
  have hswap := (Measure.ae_ae_comm hmeas).mp hbound
  have hm : Measurable (fun t : UnitAddCircle => ∫⁻ z,
      pathImageCount {x | (t, x) ∈ H} (γmap z) ∂(P : Measure Z)) :=
    (hfullZ.comp measurable_swap).lintegral_prod_right' (ν := (P : Measure Z))
  filter_upwards [hswap, ae_lt_top hm hmean.ne] with t ht he
  refine ⟨he, ?_⟩
  have hsection : Measurable (fun z : Z => pathImageCount {x | (t, x) ∈ H} (γmap z)) :=
    hfullZ.comp (measurable_id.prodMk measurable_const)
  filter_upwards [ht, ae_lt_top hsection he.ne] with z hz hf
  exact no_free_hits_of_finite_count_le U Flags _ hdisj (γmap z) hf hz

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
-- module Solutions.Q146_CD.CircleDomains_Topology_MeanSigmaCompactPhysicalCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differential-weighted mean intersection bounds on an open physical
chart, exhausted by compact sets. The law may contain paths with repeats.
-/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [SecondCountableTopology X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem mean_sigmaCompact_physical_chart_circle_count_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : IsSigmaCompact A)
    (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (μ : ProbabilityMeasure C(PathTime, X))
    (hfinite : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), physicalDomainLength e y₀ γ < ∞)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1, ∫⁻ γ : C(PathTime, X),
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
        γ ∂(μ : Measure C(PathTime, X))) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂meanPhysicalOccupation e y₀ μ := by
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hcov⟩ := hA
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hφA : MeasurableSet (φ '' A) := by
    obtain ⟨K, hK, hcov⟩ := hA.image hφ
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  let g : Y → ℝ≥0∞ := (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖)
  have hg : Measurable g :=
    (((measurable_fderiv ℝ f).norm.ennreal_ofReal).comp hjm).indicator hφA
  have hcount := measurable_sigmaCompact_chart_circle_count (π ∘ φ) (hπ.comp hφ) hA f
    (hf.continuousOn.mono hAD)
  have hm : Measurable (fun p : C(PathTime, X) × ℝ =>
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (p.2 : UnitAddCircle)}))
        p.1) := hcount.comp (measurable_fst.prodMk
          ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp measurable_snd))
  have hp : ∀ᵐ γ ∂(μ : Measure C(PathTime, X)), (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ) ≤
      (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ := by
    filter_upwards [hfinite] with γ hγ
    rw [show (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) =
      ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖ ∂physicalOccupationCode e y₀ γ
      from lintegral_indicator hφA _, physicalOccupationCode_eq e y₀ ⟨γ, hγ⟩]
    exact smooth_physical_chart_circle_count_le hcoarea e hU y₀ π hπ he φ hφ hAm
      hφA hAG hAD hD j hjm hj B hB ⟨γ, hγ⟩ hf
  calc
    _ = ∫⁻ γ : C(PathTime, X), ∫⁻ t in Ico (0 : ℝ) 1,
        pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}))
          γ ∂volume ∂(μ : Measure C(PathTime, X)) :=
      lintegral_lintegral_swap (hm.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ γ : C(PathTime, X), (B : ℝ≥0∞) * ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ
        ∂(μ : Measure C(PathTime, X)) := lintegral_mono_ae hp
    _ = (B : ℝ≥0∞) * ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        lintegral_physicalOccupationCode e hU y₀ μ g hg]
    _ = _ := by rw [show g = (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) from rfl, lintegral_indicator hφA]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FiniteRealChartIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite generic intersections on a bounded physical chart follow
from the actual L2 occupation density and the coordinate's differential
energy. No simplicity of the sampled path is needed.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_9 : BorelSpace Sphere := ⟨rfl⟩
theorem mean_real_chart_circle_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {A D K : Set ℂ} (hA : IsSigmaCompact A) (hK : IsCompact K) (hAK : A ⊆ K)
    (hAG : ∀ z ∈ A, (z : Sphere) ∈ G) (hAD : A ⊆ D) (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' (A ∩ {z | (f z : UnitAddCircle) = t}))
        γ ∂(μ : Measure _)) < ∞ := by
  obtain ⟨B, hB⟩ := finiteCoord_lipschitz_on_compact_chart hK
  have hAm : MeasurableSet A := by
    obtain ⟨Q, hQ, hcov⟩ := hA
    rw [← hcov]
    exact MeasurableSet.iUnion fun n => (hQ n).measurableSet
  have hcoeA : MeasurableSet (((↑) : ℂ → Sphere) '' A) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hAm
  let k : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖fderiv ℝ f z‖
  let g := localizedSphericalChartWeight B A k
  have hk : Measurable k := (measurable_fderiv ℝ f).norm.ennreal_ofReal
  have hg : Measurable g := measurable_localizedSphericalChartWeight B hAm hk
  have hg2 : (∫⁻ y, g y ^ 2 ∂sphericalArea) < ∞ :=
    localizedSphericalChartWeight_square_finite B hAm hk
      ((lintegral_mono_set hAD).trans_lt henergy)
  have hcost : (∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ) < ∞ := by
    rw [← lintegral_physicalOccupationCode e hU y₀ μ g hg]
    exact (lintegral_physical_cost_le_square_norms e hU y₀ μ sphericalArea ρ g hρ hg hocc).trans_lt
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hρ2.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg2.ne))
  have hbound := mean_sigmaCompact_physical_chart_circle_count_le hcoarea e hU y₀ π hπ he
    ((↑) : ℂ → Sphere) OnePoint.continuous_coe hA hAG hAD hD finiteCoord
    measurable_finiteCoord (fun z _ => finiteCoord_coe z) B (hB.mono (image_mono hAK))
    μ hfinite hf
  have hi : (∫⁻ t in Ico (0 : ℝ) 1, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) ''
        (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ ∂(μ : Measure _)) < ∞ := by
    apply hbound.trans_lt
    simpa only [g, localizedSphericalChartWeight, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      lintegral_indicator hcoeA] using hcost
  have hc := measurable_sigmaCompact_chart_circle_count
    (fun z : ℂ => π (z : Sphere)) (hπ.comp OnePoint.continuous_coe) hA f
      (hf.continuousOn.mono hAD)
  have hm := (hc.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure _))
  have heq := (AddCircle.measurePreserving_mk (1 : ℝ) 0).lintegral_comp hm
  rw [restrict_Ico_eq_restrict_Ioc] at hi
  simp only [zero_add] at heq
  dsimp only [Function.comp_def, Prod.swap] at heq
  exact heq ▸ hi

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleChartIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two branch cuts cover a smooth circle coordinate. Each branch has
the intrinsic differential, so scalar coarea gives a finite expected
intersection count without a global real lift. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_10 : BorelSpace Sphere := ⟨rfl⟩
theorem mean_circle_chart_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K)
    (hAG : ∀ z ∈ K ∩ D, (z : Sphere) ∈ G)
    {f : ℂ → UnitAddCircle} (hf : SmoothCircleOn f D)
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (a b : ℝ) (hab : (a : UnitAddCircle) ≠ (b : UnitAddCircle)) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ γ,
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' ((K ∩ D) ∩ {z | f z = θ}))
        γ ∂(μ : Measure _)) < ∞ := by
  let O (c : ℝ) := D ∩ f ⁻¹' ({(c : UnitAddCircle)}ᶜ)
  let A (c : ℝ) := K ∩ O c
  let S (c : ℝ) (θ : UnitAddCircle) := (fun z : ℂ => π (z : Sphere)) ''
    (A c ∩ {z | (circleBranch f c z : UnitAddCircle) = θ})
  have hO (c : ℝ) : IsOpen (O c) :=
    hf.continuousOn.isOpen_inter_preimage hD isClosed_singleton.isOpen_compl
  have hσ (c : ℝ) : IsSigmaCompact (A c) := by
    let : LocallyCompactSpace (O c) := (hO c).locallyCompactSpace
    have hs : IsSigmaCompact (O c) := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨Q, hQ, hcov⟩ := hs
    refine ⟨fun n => K ∩ Q n, fun n => (hQ n).inter_left hK.isClosed, ?_⟩
    rw [← inter_iUnion, hcov]
  have hcut (c : ℝ) : ∀ z ∈ O c, f z ≠ (c : UnitAddCircle) := fun _ hz => hz.2
  have hbranch (c : ℝ) := smooth_circleBranch hf c
    (show O c ⊆ D from inter_subset_left) (hcut c)
  have hmean (c : ℝ) : (∫⁻ θ : UnitAddCircle, ∫⁻ γ,
      pathImageCount (S c θ) γ ∂(μ : Measure _)) < ∞ :=
    mean_real_chart_circle_count_finite hcoarea e hU y₀ π hπ he (hσ c) hK
      inter_subset_left (fun z hz => hAG z ⟨hz.1, hz.2.1⟩) inter_subset_right (hO c)
      ((hbranch c).of_le (by norm_num))
      ((circleBranch_energy_le hf c (hO c).measurableSet inter_subset_left (hcut c) volume).trans_lt henergy)
      μ hfinite ρ hρ hocc hρ2
  have hmeas (c : ℝ) (θ : UnitAddCircle) : Measurable
      (fun γ : C(PathTime, Sphere) => pathImageCount (S c θ) γ) :=
    (measurable_sigmaCompact_chart_circle_count (fun z : ℂ => π (z : Sphere))
      (hπ.comp OnePoint.continuous_coe) (hσ c) (circleBranch f c)
      ((hbranch c).continuousOn.mono inter_subset_right)).comp
        (measurable_id.prodMk measurable_const)
  have hcover (θ : UnitAddCircle) (γ : C(PathTime, Sphere)) :
      pathImageCount ((fun z : ℂ => π (z : Sphere)) '' ((K ∩ D) ∩ {z | f z = θ})) γ ≤
        pathImageCount (S a θ) γ + pathImageCount (S b θ) γ := by
    apply pathImageCount_le_of_cover
    rintro x ⟨_, z, hz, rfl⟩
    by_cases hza : f z ≠ (a : UnitAddCircle)
    · exact Or.inl ⟨z, ⟨⟨hz.1.1, hz.1.2, hza⟩, by simpa only [coe_circleBranch] using hz.2⟩, rfl⟩
    · have hzb : f z ≠ (b : UnitAddCircle) := fun h => hab ((not_not.mp hza).symm.trans h)
      exact Or.inr ⟨z, ⟨⟨hz.1.1, hz.1.2, hzb⟩, by simpa only [coe_circleBranch] using hz.2⟩, rfl⟩
  calc
    _ ≤ ∫⁻ θ : UnitAddCircle, ∫⁻ γ,
        pathImageCount (S a θ) γ + pathImageCount (S b θ) γ ∂(μ : Measure _) :=
      lintegral_mono fun θ => lintegral_mono (hcover θ)
    _ = (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (S a θ) γ ∂(μ : Measure _)) +
        (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (S b θ) γ ∂(μ : Measure _)) := by
      simp_rw [lintegral_add_left (hmeas a _)]
      apply lintegral_add_left
      exact ((measurable_sigmaCompact_chart_circle_count (fun z : ℂ => π (z : Sphere))
        (hπ.comp OnePoint.continuous_coe) (hσ a) (circleBranch f a)
        ((hbranch a).continuousOn.mono inter_subset_right)).comp measurable_swap).lintegral_prod_right'
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hmean a, hmean b⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodDomainIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact mask away from the image of infinity has a compact
physical inverse image. This converts the two-cut coarea estimate into
finite expected domain intersections of a masked period level. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_11 : BorelSpace Sphere := ⟨rfl⟩
theorem mean_masked_circle_domain_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (M : Set Sphere) (hM : IsClosed M) (hinfty : π OnePoint.infty ∉ M)
    (H : UnitAddCircle → Set Sphere) (w : Sphere → UnitAddCircle)
    (hlevel : ∀ θ x, x ∈ U ∩ H θ → x ∈ M ∧ w x = θ)
    (D : Set ℂ) (hD : IsOpen D) (hDG : ∀ z ∈ D, (z : Sphere) ∈ G)
    (hcover : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ M → z ∈ D)
    (f : ℂ → UnitAddCircle) (hf : SmoothCircleOn f D)
    (hpullback : ∀ z ∈ D, f z = w (π (z : Sphere)))
    (henergy : (∫⁻ z in D, ENNReal.ofReal ‖circleFDeriv f z‖ ^ 2) < ∞)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ γ, pathImageCount (U ∩ H θ) γ ∂(μ : Measure _)) < ∞ := by
  let K := ((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' M)
  have hK : IsCompact K := isCompact_finite_preimage (hM.preimage hπ) hinfty
  have hcuts : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro heq
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hhalf).mp heq
    norm_num at hh
  have hmean := mean_circle_chart_count_finite hcoarea e hU y₀ π hπ he hD hK
    (fun z hz => hDG z hz.2) hf henergy μ hfinite ρ hρ hocc hρ2 0 (1 / 2) hcuts
  apply lt_of_le_of_lt _ hmean
  apply lintegral_mono
  intro θ
  apply lintegral_mono
  intro γ
  apply pathImageCount_mono_target
  intro x hx
  have hxM := (hlevel θ x hx).1
  obtain ⟨z, hz, hzx⟩ := quotient_neighborhood_chart_covers e π he hinfty x ⟨hx.1, hxM⟩
  have hzD := hcover z hz.1 hz.2
  refine ⟨z, ⟨⟨hz.2, hzD⟩, ?_⟩, hzx⟩
  change f z = θ
  rw [hpullback z hzD, hzx]
  exact (hlevel θ x hx).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PeriodDomainValues
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the physical domain, the assembled period bands are the actual
circle-valued coordinate. Only continuity in the local patch is needed. -/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_continuousAt
    {X : Type*} [TopologicalSpace X] {D : Set X} {f : X → ℝ}
    {x : X} (hf : ContinuousAt f x) (hx : x ∈ D) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D f ↔ (f x : UnitAddCircle) = θ := by
  have hband (t : ℝ) : (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = f x := by
    constructor
    · intro ht
      obtain ⟨a, b, s, ha, hb, _, heq⟩ := mem_intervalFiberHull_iff.mp ht
      rw [clusterGraph_fiber_eq_of_continuousAt hf ha,
        clusterGraph_fiber_eq_of_continuousAt hf hb] at heq
      nlinarith [heq]
    · rintro rfl
      exact subset_intervalFiberHull _ (subset_closure ⟨x, hx, rfl⟩)
  constructor
  · rintro ⟨⟨y, t⟩, ht, he⟩
    have hy : y = x := congrArg Prod.fst he
    subst y
    simpa only [(hband t).mp ht] using congrArg Prod.snd he
  · intro he
    exact ⟨(x, f x), (hband (f x)).mpr rfl, Prod.ext rfl he⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedTupleCompatibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-tuple comparison uses the inherited coordinate order,
which need not be the order of its natural-number enumeration. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [TopologicalSpace X]

local instance localInst_r5b7c64_12 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩
theorem ae_ranked_finite_tuple_ordered_compatibility
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : RankedLevelNullCompatibility rank H F) {n m : ℕ}
    (l : Fin n → ℕ) (r : Fin m → ℕ) :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))),
      ∀ j : Fin m, ∀ A : Finset (Fin n), (∀ k ∈ A, rank (l k) < rank (r j)) →
        ∀ x ∈ F, (p.2 j, x) ∈ H (r j) →
          ¬ (connectedComponentIn (⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)}) x).Nontrivial := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro A
  by_cases horder : ∀ k ∈ A, rank (l k) < rank (r j)
  · let e : Fin (Fintype.card A) → Fin n := fun k => ((Fintype.equivFin A).symm k).val
    have he : Injective e := Subtype.val_injective.comp (Fintype.equivFin A).symm.injective
    have hp := hP (r j) (Fintype.card A) (l ∘ e) (fun k =>
      horder (e k) ((Fintype.equivFin A).symm k).property)
    have hproj : MeasurePreserving
        (fun p : (Fin n → UnitAddCircle) × (Fin m → UnitAddCircle) => (p.2 j, p.1 ∘ e))
        (volume.prod volume) (volume.prod volume) := by
      exact Measure.measurePreserving_swap.comp
        ((torus_projection_measurePreserving e he).prod
          (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j))
    have hzero := hproj.quasiMeasurePreserving.preimage_null hp
    have hgood : ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
        (volume : Measure (Fin m → UnitAddCircle))),
        (p.2 j, p.1 ∘ e) ∉ freeComponentFailure F (levelRelation H (r j))
          (levelRelation H) (l ∘ e) := by
      rw [ae_iff]
      simpa only [Set.preimage, not_not, ofPred_mem_eq] using hzero
    filter_upwards [hgood] with p hp
    intro _ x hx hj hnt
    apply hp
    have hset : {y | (y, p.1 ∘ e) ∈ finiteLevelUnionGraph (levelRelation H) (l ∘ e)} =
        ⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)} := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := mem_iUnion.mp hy
        exact mem_iUnion₂.mpr ⟨e k, ((Fintype.equivFin A).symm k).property, hk⟩
      · intro hy
        obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
        refine mem_iUnion.mpr ⟨(Fintype.equivFin A) ⟨k, hk⟩, ?_⟩
        change (p.1 (e ((Fintype.equivFin A) ⟨k, hk⟩)), y) ∈
          H (l (e ((Fintype.equivFin A) ⟨k, hk⟩)))
        simpa only [e, Equiv.symm_apply_apply, mem_ofPred_eq] using hyk
    refine ⟨(x, p.2 j, p.1 ∘ e), ⟨hx, hj, ?_⟩, rfl⟩
    change (connectedComponentIn {y | (y, p.1 ∘ e) ∈
      finiteLevelUnionGraph (levelRelation H) (l ∘ e)} x).Nontrivial
    rwa [hset]
  · exact Eventually.of_forall fun _ h => (horder h).elim


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RankedTagTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Free tag contacts are excluded by the largest inherited label in a
finite tuple, irrespective of the enumeration used to encode the tuple. -/
open Set Function
open scoped Topology Classical
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem tag_impossible_below_ranked_level
    {I : Type*} [LinearOrder I] (rank : ℕ → I)
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (j : ℕ)
    (hbelow : ∀ k, (q.2.2.1 k, γ t) ∈ H (q.2.1 k) → rank (q.2.1 k) < rank j)
    (hcompat : ∀ A : Finset (Fin (q.1 + 1)), (∀ k ∈ A, rank (q.2.1 k) < rank j) →
      ¬ (connectedComponentIn (⋃ k ∈ A, {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)})
        (γ t)).Nontrivial) : False := by
  let L : Fin (q.1 + 1) → Set X := fun k => {x | (q.2.2.1 k, x) ∈ H (q.2.1 k)}
  let A : Finset (Fin (q.1 + 1)) := Finset.univ.filter (fun k => γ t ∈ L k)
  have hx : γ t ∈ ⋃ k, L k := mem_iUnion.mpr (hcontain t hl hr)
  have hxA : γ t ∈ ⋃ k ∈ A, L k := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩, hk⟩
  have he : (⋃ k ∈ (Finset.univ : Finset (Fin (q.1 + 1))),
      ⋃ (_ : γ t ∈ L k), L k) = ⋃ k ∈ A, L k := by
    ext x
    simp only [mem_iUnion, exists_prop, Finset.mem_univ, true_and, A, Finset.mem_filter]
  have hsmall : connectedComponentIn (⋃ k ∈ A, L k) (γ t) = {γ t} :=
    (Set.not_nontrivial_iff.mp (hcompat A (fun k hk =>
      hbelow k (Finset.mem_filter.mp hk).2))).eq_singleton_of_mem (mem_connectedComponentIn hxA)
  have hsingle : connectedComponentIn (⋃ k, L k) (γ t) = {γ t} := by
    have h := component_finite_union_eq_singleton Finset.univ L
      (fun k _ => (hH _).preimage (continuous_const.prodMk continuous_id))
      (by simpa only [Finset.mem_univ, iUnion_true] using hx)
      (by rw [he]; exact hsmall)
    simpa only [Finset.mem_univ, iUnion_true] using h
  have hn := active_tag_nontrivial_component H γ q hshape hcontain t hl hr
  rw [hsingle] at hn
  exact Set.not_nontrivial_singleton hn


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedIndependentLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent-level tag estimates in the inherited coordinate order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical
noncomputable section
namespace CircleDomainRigidity

theorem active_tag_singleton_at_ranked_level
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (H : ℕ → Set (UnitAddCircle × X)) (hH : ∀ i, IsClosed (H i))
    (Free : Set X) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q))
    (hx : γ t ∈ Free)
    (hunique : ∀ i a b, (a, γ t) ∈ H i → (b, γ t) ∈ H i → a = b)
    (i : ℕ) (θ : UnitAddCircle) (hθ : (θ, γ t) ∈ H i)
    (hc : RankedTuplePairCompatible rank H Free (tagDataTuple q) (singleLevelTuple i θ)) :
    ¬ (connectedComponentIn {x | (θ, x) ∈ H i} (γ t)).Nontrivial := by
  intro hnt
  apply tag_impossible_below_ranked_level rank H hH γ q hshape hcontain t hl hr i
  · intro k hk
    rcases lt_trichotomy (rank (q.2.1 k)) (rank i) with hlt | he | hgt
    · exact hlt
    · have hei := hrank he
      have heq : q.2.2.1 k = θ := hunique i _ _ (hei ▸ hk) hθ
      exact (hc.1 k 0 hei heq).elim
    · have hh := hc.2.2 k (Finset.univ : Finset (Fin 1))
        (fun _ _ => hgt) (γ t) hx hk
      apply False.elim
      have hset : (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) =
          {y | (θ, y) ∈ H i} := by
        ext y
        constructor
        · intro hy
          obtain ⟨_, _, hy⟩ := mem_iUnion₂.mp hy
          exact hy
        · intro hy
          exact mem_iUnion₂.mpr ⟨0, Finset.mem_univ _, hy⟩
      change ¬ (connectedComponentIn
        (⋃ k ∈ (Finset.univ : Finset (Fin 1)), {y | (θ, y) ∈ H i}) (γ t)).Nontrivial at hh
      rw [hset] at hh
      exact hh hnt
  · intro A hA
    exact hc.2.1 0 A hA (γ t) hx hθ

theorem tupleReference_ranked_single_level_incompatible_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L)
    {X : Type*} [TopologicalSpace X]
    (H : ℕ → Set (UnitAddCircle × X)) (Free : Set X)
    (hP : RankedLevelNullCompatibility rank H Free)
    (ω : TupleType → ℝ≥0∞) (i : ℕ) :
    ((tupleReference ω).prod (volume : Measure UnitAddCircle))
      {p | ¬ RankedTuplePairCompatible rank H Free p.1 (singleLevelTuple i p.2)} = 0 := by
  apply tupleReference_product_right_null
  intro q
  let r : TupleType := ⟨0, fun _ => i⟩
  have hleft := ae_ranked_finite_tuple_ordered_compatibility rank H Free hP q.2 r.2
  have hright := Measure.measurePreserving_swap.quasiMeasurePreserving.ae
    (ae_ranked_finite_tuple_ordered_compatibility rank H Free hP r.2 q.2)
  have hg : ∀ᵐ p ∂((volume : Measure (Fin (q.1 + 1) → UnitAddCircle)).prod
      (volume : Measure (Fin 1 → UnitAddCircle))),
      RankedTuplePairCompatible rank H Free (tupleFiber q p.1) (tupleFiber r p.2) := by
    filter_upwards [ae_torus_pair_distinct, hleft, hright] with p hp hl hr
    exact ⟨fun a b _ => hp a b, hl, hr⟩
  have he : MeasurePreserving
      (Prod.map (id : (Fin (q.1 + 1) → UnitAddCircle) → _)
        (MeasurableEquiv.funUnique (Fin 1) UnitAddCircle).symm)
      (volume.prod (volume : Measure UnitAddCircle)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (MeasureTheory.volume_preserving_funUnique (Fin 1) UnitAddCircle).symm
  have hh := he.quasiMeasurePreserving.ae hg
  exact ae_iff.mp hh

theorem ae_ranked_tag_contacts_singleton_at_independent_level
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]
    (d : PathCodeData X Y) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set X) (hP : RankedLevelNullCompatibility rank d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k q, Γ.val.2 k = Sum.inr q → ∀ t,
        tagLeft (Sum.inr q) < t → t < tagRight (Sum.inr q) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  have hg := ae_active_slots_avoid_independent_null d P (tupleReference ω) volume hτ
    {p | ¬ RankedTuplePairCompatible rank d.levels Free p.1 (singleLevelTuple i p.2)}
    (tupleReference_ranked_single_level_incompatible_null rank d.levels Free hP ω i)
  filter_upwards [hg] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k q hq t hl hr hx hlevel
  have hcompat : RankedTuplePairCompatible rank d.levels Free (tagDataTuple q) (singleLevelTuple i θ) :=
    not_not.mp (hθ k q hq)
  exact active_tag_singleton_at_ranked_level rank hrank d.levels hH Free Γ.val.1 q
    (hq ▸ (Γ.property.1.2.1 k).1) (hq ▸ (Γ.property.1.2.1 k).2.1)
    t hl hr hx (hunique _ hx) i θ hlevel hcompat


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RankedCodeTraces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic prior-level intersections for a code whose natural labels carry
an independent inherited order. Physical coarea and local trace estimates
are unchanged; only the finite-tuple comparison uses the rank. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_16
omit [BorelSpace C(PathTime, Sphere)] in
theorem ranked_ae_code_level_singleton_on_tags
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : RankedLevelNullCompatibility rank d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k t, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) →
        Γ.val.1 t ∈ Free → (θ, Γ.val.1 t) ∈ d.levels i →
        ¬ (connectedComponentIn {x | (θ, x) ∈ d.levels i} (Γ.val.1 t)).Nontrivial := by
  filter_upwards [ae_ranked_tag_contacts_singleton_at_independent_level rank hrank d hH Free hP hunique
    P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k t ht hx hxt
  cases hslot : Γ.val.2 k with
  | inl u =>
      have hn : ¬ tagLeft (Sum.inl u) < t := not_lt_of_ge le_top
      exact (hn (hslot ▸ ht.1)).elim
  | inr q => exact hθ k q hslot t (hslot ▸ ht.1) (hslot ▸ ht.2) hx hxt

theorem ranked_ae_code_local_band_tag_trace_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable)
    (V : Set Sphere) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ closure V)
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f (d.quotientDomain ∩ V))
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤ m z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, m z = 0)
    (hH : ∀ i, IsClosed (d.levels i))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω) (i : ℕ)
    (hlevel : ∀ z ∈ V, ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain f ↔ (θ, z) ∈ d.levels i)
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (d.quotientDomainᶜ \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) → t ∈ Ico c (c + 1)) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume ((trace ∘ Γ.val.1) '' ((Γ.val.1 ⁻¹' (d.quotientDomainᶜ \ Flags)) ∩
        (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V))) = 0 := by
  apply ae_all_iff.mpr
  intro k
  apply ae_parameter_local_band_tag_null_trace hsard hsch hG hU hdense π hπ
    hclosed hsurj hr d.domainEquiv d.basePoint he hTD hbad hV hinfty hFlags hM hf
    (fun θ => {x | (θ, x) ∈ d.levels i})
    (fun θ => (hH i).preimage (continuous_const.prodMk continuous_id)) hlevel
    hv henergy P (codePath d) (measurable_codePath d) (codePathLaw d P) rfl
    (Eventually.of_forall fun Γ => Γ.property.1.1) ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2 m hm hweight hvisits
    hband hmFree (fun Γ => Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)))
    (fun _ => isOpen_Ioo) trace htrace hbranch
  filter_upwards [ranked_ae_code_level_singleton_on_tags rank hrank d hH _ hP hunique P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  exact fun t ht => hθ k t ht


theorem ranked_ae_code_branch_free_level_incidence_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {I : Type*} [Countable I] (V : I → Set Sphere) (hV : ∀ j, IsOpen (V j))
    (hinfty : ∀ j, π OnePoint.infty ∉ closure (V j))
    (f : I → Sphere → ℝ) (bound : I → ℝ)
    (hbound : ∀ j z, z ∈ d.quotientDomain → |f j z| ≤ bound j)
    (hf : ∀ j, ContinuousOn (f j) (d.quotientDomain ∩ V j))
    (hv : ∀ j, ContDiffOn ℝ 1 (fun z : ℂ => f j (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V j))
    (henergy : ∀ j, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V j,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f j (π (z : Sphere))) z‖ ^ 2) < ∞)
    (hband : ∀ j z, z ∈ d.quotientDomainᶜ ∩ V j → ENNReal.ofReal
      (limsup (f j) (𝓝[d.quotientDomain] z) - liminf (f j) (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (c : I → ℝ) (hbranch : ∀ j z, z ∈ V j → ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) → t ∈ Ico (c j) (c j + 1))
    (hlevel : ∀ j z, z ∈ V j → ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i)
    (hcover : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ θ, (θ, x) ∈ d.levels i → ∃ j, x ∈ V j) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let trace (j : I) := realBoundaryTrace d.quotientDomain (f j)
  have htrace (j : I) (x : Sphere) (hx : x ∈ (d.quotientDomainᶜ \ Flags) ∩ V j) :
      ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ t = trace j x := by
    apply real_band_fiber_eq_trace_of_zero_width (hbound j)
      (by rw [hdense.closure_eq]; trivial)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp
      ((hband j x ⟨hx.1.1, hx.2⟩).trans_eq (hmFree x hx.1)))
  apply ae_code_free_incidence_null_of_local_real_traces d P i (d.quotientDomainᶜ \ Flags)
    (fun x hx => hdust.symm ▸ hx.1) hm hweight hvisits hdeleteCover
    (fun n => disjoint_left.mpr fun x hx hxn => hx.2 (hdeletions n hxn))
    V f trace hcover hlevel htrace
  intro j
  exact ranked_ae_code_local_band_tag_trace_null rank hrank hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags (V j) (hV j) (hinfty j)
    (f j) (hbound j) (hf j) (hv j) (henergy j) P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits
    (fun z hz => hband j z ⟨hFlagsB hz.1, hz.2⟩) hmFree hH hP hunique ω hτ i
    (hlevel j) (trace j) (htrace j) (hbranch j)


theorem ranked_ae_code_period_free_level_incidence_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {I : Type*} [Countable I] (V : I → Set Sphere) (hV : ∀ j, IsOpen (V j))
    (M : Set Sphere) (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags)
    (hmask : ∀ θ x, (θ, x) ∈ d.levels i → x ∈ M)
    (hcoverM : M \ {b} ⊆ ⋃ j, V j)
    (f : I → Sphere → ℝ) (bound : I → ℝ)
    (hbound : ∀ j z, z ∈ d.quotientDomain → |f j z| ≤ bound j)
    (hf : ∀ j, ContinuousOn (f j) (d.quotientDomain ∩ V j))
    (hv : ∀ j, ContDiffOn ℝ 1 (fun z : ℂ => f j (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V j))
    (henergy : ∀ j, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V j,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f j (π (z : Sphere))) z‖ ^ 2) < ∞)
    (hband : ∀ j z, z ∈ (d.quotientDomainᶜ ∩ M) ∩ V j → ENNReal.ofReal
      (limsup (f j) (𝓝[d.quotientDomain] z) - liminf (f j) (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hlevel : ∀ j z, z ∈ M ∩ V j → ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let F (j : I) := Free ∩ (M ∩ V j)
  let a (j : I) := realBoundaryTrace d.quotientDomain (f j)
  have htrace (j : I) (x : Sphere) (hx : x ∈ F j) :
      ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain (f j)) ↔ t = a j x := by
    apply real_band_fiber_eq_trace_of_zero_width (hbound j)
      (by rw [hdense.closure_eq]; trivial)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp
      ((hband j x ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2⟩).trans_eq (hmFree x hx.1)))
  have hinside (x : Sphere) (hx : x ∈ Free ∩ M) : x ∈ interior M := by
    by_contra hn
    exact hx.1.1 (hboundary ⟨hx.2, hn⟩)
  have hselect (j : I) := countable_narrow_real_band_cover_closure
    (F := F j) (a := a j) (hbound j) ((hV j).inter isOpen_interior)
    (fun x hx => ⟨hx.2.2, hinside x ⟨hx.1, hx.2.1⟩⟩)
    (fun x hx t ht => (htrace j x hx t).mp ht)
  choose S N hSF hSc hcov hN using hselect
  let : ∀ j, Countable (S j) := fun j => (hSc j).to_subtype
  let J := Σ j, S j
  have hNV (q : J) : N q.1 q.2.val ⊆ V q.1 :=
    fun x hx => ((hN q.1 q.2.val q.2.property).2.2.1 (subset_closure hx)).1
  have hNM (q : J) : N q.1 q.2.val ⊆ M :=
    fun x hx => interior_subset (((hN q.1 q.2.val q.2.property).2.2.1 (subset_closure hx)).2)
  apply ranked_ae_code_branch_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    (fun q : J => N q.1 q.2.val)
    (fun q => (hN q.1 q.2.val q.2.property).1)
    (fun q hp => hinftyM (interior_subset
      (((hN q.1 q.2.val q.2.property).2.2.1 hp).2)))
    (fun q => f q.1) (fun q => bound q.1) (fun q => hbound q.1)
    (fun q => (hf q.1).mono (fun x hx => ⟨hx.1, hNV q hx.2⟩))
    (fun q => (hv q.1).mono (fun x hx => ⟨hx.1, hNV q hx.2⟩))
    (fun q => (lintegral_mono_set (show
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' N q.1 q.2.val) ⊆
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V q.1) from
        fun x hx => ⟨hx.1, hNV q hx.2⟩)).trans_lt (henergy q.1))
    (fun q z hz => hband q.1 z ⟨⟨hz.1, hNM q hz.2⟩, hNV q hz.2⟩)
    (fun q => a q.1 q.2.val - 1 / 2)
    (fun q => (hN q.1 q.2.val q.2.property).2.2.2)
    (fun q z hz => hlevel q.1 z ⟨hNM q hz, hNV q hz⟩)
  intro x hx θ hθ
  have hxM := hmask θ x hθ
  have hxb : x ≠ b := fun heq => hx.2 (heq ▸ hb)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp (hcov j ⟨hx, hxM, hj⟩)
  exact ⟨⟨j, ⟨y, hyS⟩⟩, hxy⟩


theorem ranked_code_period_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {I : Type*} [Countable I] (V : I → Set Sphere) (hV : ∀ j, IsOpen (V j))
    (M : Set Sphere) (hM : IsClosed M) (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags) (hbWeight : 1 ≤ d.levelWeights i b)
    (hmask : ∀ θ x, (θ, x) ∈ d.levels i → x ∈ M)
    (hcoverM : M \ {b} ⊆ ⋃ j, V j)
    (f : I → Sphere → ℝ) (bound : I → ℝ)
    (hbound : ∀ j z, z ∈ d.quotientDomain → |f j z| ≤ bound j)
    (hf : ∀ j, ContinuousOn (f j) (d.quotientDomain ∩ V j))
    (hv : ∀ j, ContDiffOn ℝ 1 (fun z : ℂ => f j (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' V j))
    (henergy : ∀ j, (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' V j,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f j (π (z : Sphere))) z‖ ^ 2) < ∞)
    (hband : ∀ j z, z ∈ (d.quotientDomainᶜ ∩ M) ∩ V j → ENNReal.ofReal
      (limsup (f j) (𝓝[d.quotientDomain] z) - liminf (f j) (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hlevel : ∀ j z, z ∈ M ∩ V j → ∀ θ,
      (z, θ) ∈ circleBandGraph d.quotientDomain (f j) ↔ (θ, z) ∈ d.levels i)
    (w : Sphere → UnitAddCircle)
    (hw : ∀ j x, x ∈ d.quotientDomain ∩ V j → (f j x : UnitAddCircle) = w x)
    (D : Set ℂ) (hD : IsOpen D) (hDG : ∀ z ∈ D, (z : Sphere) ∈ d.physicalDomain)
    (hDcover : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → π (z : Sphere) ∈ M → z ∈ D)
    (F : ℂ → UnitAddCircle) (hF : FiniteTransfer.SmoothCircleOn F D)
    (hFpull : ∀ z ∈ D, F z = w (π (z : Sphere)))
    (hFenergy : (∫⁻ z in D, ENNReal.ofReal ‖FiniteTransfer.circleFDeriv F z‖ ^ 2) < ∞) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ ∧
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  have hfree := ranked_ae_code_period_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    V hV M hinftyM hboundary b hb hmask hcoverM f bound hbound hf hv henergy hband hlevel
  have hfinite : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
    change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)).mpr
    exact Eventually.of_forall fun Γ => Γ.property.1.1
  have hdomLevel (θ : UnitAddCircle) (x : Sphere)
      (hx : x ∈ d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) : x ∈ M ∧ w x = θ := by
    have hxM := hmask θ x hx.2
    have hxb : x ≠ b := fun heq => hFlagsB hb (heq ▸ hx.1)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
    have hcg := (hlevel j x ⟨hxM, hj⟩ θ).mpr hx.2
    have heq := (circleBandGraph_of_continuousAt
      ((hf j).continuousAt ((hU.inter (hV j)).mem_nhds ⟨hx.1, hj⟩)) hx.1 θ).mp hcg
    exact ⟨hxM, (hw j x ⟨hx.1, hj⟩).symm.trans heq⟩
  have hdom := mean_masked_circle_domain_count_finite hcoarea d.domainEquiv hU d.basePoint
    π hπ he M hM hinftyM (fun θ => {x | (θ, x) ∈ d.levels i}) w hdomLevel
    D hD hDG hDcover F hF hFpull hFenergy (codePathLaw d P) hfinite ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2
  have hvol : ∀ x ∈ Flags, volume {θ : UnitAddCircle | (θ, x) ∈ d.levels i} ≤ d.levelWeights i x := by
    intro x hx
    by_cases hxM : x ∈ M
    · by_cases hxb : x = b
      · subst x
        exact (measure_mono (subset_univ _)).trans (by simpa [AddCircle.measure_univ] using hbWeight)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcoverM ⟨hxM, hxb⟩)
        have heq : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} =
            {θ | (x, θ) ∈ circleBandGraph d.quotientDomain (f j)} :=
          Set.ext fun θ => (hlevel j x ⟨hxM, hj⟩ θ).symm
        rw [heq]
        exact (volume_circleBandGraph_incidence_le_budget (hbound j)
          (by rw [hdense.closure_eq]; trivial) le_rfl).trans
            (hband j x ⟨⟨hFlagsB hx, hxM⟩, hj⟩)
    · have hempty : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun θ hθ => hxM (hmask θ x hθ)
      rw [hempty, measure_empty]
      exact bot_le
  have hflag := mean_flag_intersection_count_finite_of_support (hH i) Flags hFlags
    (d.levelWeights i) hvol (codePathLaw d P) hm hweight hvisits
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hbnd := mean_parameter_level_count_le_of_no_free_hits (hH i)
    d.quotientDomain Flags hσU hFlags P (codePath d) (measurable_codePath d) hfree'
  have hDmeas := measurable_sigmaCompact_restricted_relation_path_count hσU
    ((hH i).preimage continuous_swap)
  have hFmeas := measurable_flag_intersection_count (hH i) Flags hFlags
  have hdint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hDmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  have hfint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  have hmean : (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ := by
    apply hbnd.trans_lt
    apply ENNReal.add_lt_top.mpr
    constructor
    · simpa only [hdint] using hdom
    · simpa only [hfint] using hflag
  refine ⟨hmean, ?_⟩
  have hdisj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr fun x hx hxf => hFlagsB hxf hx
  simpa only [codePath] using ae_level_parameter_free_avoidance (hH i)
    d.quotientDomain Flags hσU hFlags hdisj P (codePath d) (measurable_codePath d) hfree' hmean


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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureBaseCodeOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
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
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanGraphGeometry
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothed mean has the local real-band width and free-fiber
properties used by mixed grid geometry. These are derived from its
retained correction and the original arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_18
theorem SmoothMeanPeriodData.branch_width_le_hit
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) F G U S M b π)
    (i : Q.Index) {x : Sphere} (hx : x ∈ M \ U) (hxi : x ∈ Q.patch i) :
    limsup (Q.branch i) (𝓝[U] x) - liminf (Q.branch i) (𝓝[U] x) ≤
      (η : Measure A).real {γ | x ∈ range γ.val} := by
  have hxS : x ∈ S := Q.patch_closure i (subset_closure hxi)
  let L : Sphere → ClosedUpperHalfPlane := fun z =>
    upperHalfPlaneClamp (logarithmicCutChart (Q.angle i) (F z))
  have hLC : ContinuousAt L x := continuous_upperHalfPlaneClamp.continuousAt.comp
    ((Q.log_continuous i).continuousAt
      (mem_of_superset ((Q.patch_open i).mem_nhds hxi) subset_closure))
  have him : 0 < (logarithmicCutChart (Q.angle i) (F x)).im :=
    logarithmicCutChart_im_pos (Q.angle i) (h0 x hxS) (h1 x hx)
  have hLv : (L x).val = logarithmicCutChart (Q.angle i) (F x) :=
    upperHalfPlaneClamp_val him.le
  have hproj : diskRayProjection (L x).val = F x := by
    rw [hLv]
    exact logarithmicCutChart_projection (Q.angle i) (h0 x hxS)
  have heq : (fun z => Q.branch i z - meanGeometricIndex hsch K hKS (η.map (f := f) (by first | exact hf.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (L z))
      =ᶠ[𝓝[U] x] Q.error := by
    filter_upwards [nhdsWithin_le_nhds ((Q.patch_open i).mem_nhds hxi)] with z hz
    rw [Q.branch_value i z hz]
    exact add_sub_cancel_left _ _
  have herr := ((Q.error_vanishes x hx.2).mono_left nhdsWithin_le_nhds).congr' heq.symm
  exact (perturbed_mapped_mean_bands hsch hsep A K hK hKS η F f hf hmap x
    (fun γ => (hF γ).mono (union_subset_union Subset.rfl (singleton_subset_iff.mpr hxS)))
    U x (by rw [hdense.closure_eq]; trivial) L hLC.continuousWithinAt
    (by simpa only [hLv] using him) hproj (Q.branch i) herr).2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RealDomainIntersections
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real coordinate that vanishes outside a compact finite-plane set
has finite generic intersections throughout the physical domain. The
single zero level also accounts for the physical point at infinity.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem real_domain_nonzero_level_subset
    {G U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U)
    (π : Sphere → Sphere) (he : ∀ y : G, (e y).val = π y.val)
    (f : Sphere → ℝ) (hf : ContinuousOn f U) {K : Set ℂ}
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ G → f (π OnePoint.infty) = 0)
    {t : UnitAddCircle} (ht0 : t ≠ 0) :
    U ∩ {x | (x, t) ∈ circleBandGraph U f} ⊆
      (fun z : ℂ => π (z : Sphere)) ''
        ((K ∩ ((↑) : ℂ → Sphere) ⁻¹' G) ∩
          {z | (f (π (z : Sphere)) : UnitAddCircle) = t}) := by
  intro x hx
  let y := e.symm ⟨x, hx.1⟩
  have hy : π y.val = x := by rw [← he y]; exact congrArg Subtype.val (e.apply_symm_apply _)
  have hft : (f x : UnitAddCircle) = t := (circleBandGraph_on_open hU hf hx.1).mp hx.2
  cases hp : y.val using OnePoint.rec with
  | infty =>
      have hz : f x = 0 := by rw [← hy, hp]; exact hinfty (hp ▸ y.property)
      exact (ht0 (by simpa only [hz, AddCircle.coe_zero] using hft.symm)).elim
  | coe z =>
      have hzG : (z : Sphere) ∈ G := hp ▸ y.property
      have hzK : z ∈ K := by
        by_contra hn
        have hz : f x = 0 := by rw [← hy, hp]; exact hzero z hzG hn
        exact ht0 (by simpa only [hz, AddCircle.coe_zero] using hft.symm)
      refine ⟨z, ⟨⟨hzK, hzG⟩, ?_⟩, ?_⟩
      · change (f (π (z : Sphere)) : UnitAddCircle) = t
        rwa [← hp, hy]
      · change π (z : Sphere) = x
        rw [← hp, hy]

local instance localInst_r5b7c64_13 : BorelSpace Sphere := ⟨rfl⟩
theorem mean_real_domain_circle_count_finite
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U : Set Sphere} (hG : IsOpen G) (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (f : Sphere → ℝ) (hf : ContinuousOn f U)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere))) (((↑) : ℂ → Sphere) ⁻¹' G))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' G,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ G → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ G → f (π OnePoint.infty) = 0)
    (μ : ProbabilityMeasure C(PathTime, Sphere))
    (hfinite : ∀ᵐ γ ∂(μ : Measure _), physicalDomainLength e y₀ γ < ∞)
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanPhysicalOccupation e y₀ μ = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount (U ∩ {x | (x, t) ∈ circleBandGraph U f}) γ ∂(μ : Measure _)) < ∞ := by
  let O := ((↑) : ℂ → Sphere) ⁻¹' G
  let A := K ∩ O
  let v : ℂ → ℝ := fun z => f (π (z : Sphere))
  have hO : IsOpen O := hG.preimage OnePoint.continuous_coe
  have hσ : IsSigmaCompact A := by
    let : LocallyCompactSpace O := hO.locallyCompactSpace
    have hσO : IsSigmaCompact O := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
    obtain ⟨Q, hQ, hcov⟩ := hσO
    refine ⟨fun n => K ∩ Q n, fun n => (hQ n).inter_left hK.isClosed, ?_⟩
    rw [← inter_iUnion, hcov]
  have hm := mean_real_chart_circle_count_finite hcoarea e hU y₀ π hπ he hσ hK
    inter_subset_left (fun _ hz => hz.2) inter_subset_right hO hv henergy μ hfinite ρ hρ hocc hρ2
  have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
    simpa only [image_singleton, AddCircle.coe_zero] using
      (volume_addCircle_image_eq_zero (show (volume : Measure ℝ) {0} = 0 from measure_singleton 0))
  have ha0 : ∀ᵐ t : UnitAddCircle ∂volume, t ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not, ofPred_eq_eq_singleton] using hz)
  apply (show (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount (U ∩ {x | (x, t) ∈ circleBandGraph U f}) γ ∂(μ : Measure _)) ≤
      (∫⁻ t : UnitAddCircle, ∫⁻ γ,
        pathImageCount ((fun z : ℂ => π (z : Sphere)) ''
          (A ∩ {z | (v z : UnitAddCircle) = t})) γ ∂(μ : Measure _)) from ?_).trans_lt hm
  apply lintegral_mono_ae
  filter_upwards [ha0] with t ht0
  apply lintegral_mono
  intro γ
  exact pathImageCount_mono_target
    (real_domain_nonzero_level_subset e hU π he f hf hzero hinfty ht0) γ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_RankedRealCodeLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-coordinate generic levels with the inherited order on code labels. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem ranked_ae_code_real_level_singleton_on_tags
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (d : PathCodeData Sphere Sphere) (hH : ∀ i, IsClosed (d.levels i))
    (Free : Set Sphere) (hP : RankedLevelNullCompatibility rank d.levels Free)
    (hunique : ∀ x ∈ Free, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (P : ProbabilityMeasure (BasePathCode d)) (ω : TupleType → ℝ≥0∞)
    [SFinite (tupleReference ω)] (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (i : ℕ) (f : Sphere → ℝ)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ k t, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) →
        Γ.val.1 t ∈ Free → (Γ.val.1 t, θ) ∈ circleBandGraph d.quotientDomain f →
        ¬ (connectedComponentIn {x | (x, θ) ∈ circleBandGraph d.quotientDomain f}
          (Γ.val.1 t)).Nontrivial := by
  filter_upwards [ae_ranked_tag_contacts_singleton_at_independent_level rank hrank d hH Free hP hunique
    P ω hτ i] with Γ hΓ
  filter_upwards [hΓ] with θ hθ
  intro k t ht hx hxt
  cases hslot : Γ.val.2 k with
  | inl u =>
      have hn : ¬ tagLeft (Sum.inl u) < t := not_lt_of_ge le_top
      exact (hn (hslot ▸ ht.1)).elim
  | inr q =>
      have hs : {x | (θ, x) ∈ d.levels i} =
          {x | (x, θ) ∈ circleBandGraph d.quotientDomain f} := by
        ext x
        exact hlevel θ x
      have h := hθ k q hslot t (hslot ▸ ht.1) (hslot ▸ ht.2) hx
        ((hlevel θ _).mpr hxt)
      simpa only [hs] using h

local instance localInst_r5b7c64_14 : BorelSpace Sphere := ⟨rfl⟩
theorem ranked_ae_code_real_band_tag_trace_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere)
    (hG : IsOpen d.physicalDomain) (hU : IsOpen d.quotientDomain)
    (hdense : Dense d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (hTD : IsTotallyDisconnected d.quotientDomainᶜ)
    (hbad : ∀ p ∈ d.physicalDomainᶜ, π p ∈ d.quotientDomainᶜ)
    (Flags : Set Sphere) (hFlags : Flags.Countable) (hFlagsB : Flags ⊆ d.quotientDomainᶜ)
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f d.quotientDomain)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support m => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤ m z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, m z = 0)
    (hH : ∀ i, IsClosed (d.levels i))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ i a b,
      (a, x) ∈ d.levels i → (b, x) ∈ d.levels i → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (i : ℕ)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume (realBoundaryTrace d.quotientDomain f ''
        (Γ.val.1 '' Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          (d.quotientDomainᶜ \ Flags))) = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let a := realBoundaryTrace d.quotientDomain f
  have htrace : ∀ x ∈ Free, ∀ t,
      (x, t) ∈ intervalFiberHull (clusterGraph d.quotientDomain f) ↔ t = a x := by
    intro x hx
    apply real_band_fiber_eq_trace_of_zero_width hM (by rw [hdense.closure_eq]; exact mem_univ x)
    exact ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp ((hband x hx.1).trans_eq (hmFree x hx)))
  obtain ⟨S, V, _, hSc, hcover, hV⟩ := countable_narrow_real_band_cover_closure
    (F := Free \ {π OnePoint.infty}) hM isClosed_singleton.isOpen_compl
    (fun _ hx => hx.2) (fun x hx t ht => (htrace x hx.1 t).mp ht)
  let : Countable S := hSc.to_subtype
  have hgood := ranked_ae_code_real_level_singleton_on_tags rank hrank d hH Free hP hunique P ω hτ i f hlevel
  have hlocal : ∀ x : S, ∀ k : ℕ, ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume ((a ∘ Γ.val.1) ''
        ((Γ.val.1 ⁻¹' Free) ∩ (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          Γ.val.1 ⁻¹' V x.val))) = 0 := by
    intro x k
    have hx := hV x.val x.property
    apply ae_parameter_real_band_tag_null_trace hsard hsch hG hU hdense π hπ
      hclosed hsurj hr d.domainEquiv d.basePoint he hTD hbad hx.1
      (fun h => (hx.2.2.1 h) (mem_singleton _)) hFlags hM hf hv henergy P
      (codePath d) (measurable_codePath d) (codePathLaw d P) rfl
      (Eventually.of_forall fun Γ => Γ.property.1.1) ρ hρ
      ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2 m hm hweight hvisits
      (fun z hz => hband z (hFlagsB hz)) hmFree
      (fun Γ => Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)))
      (fun _ => isOpen_Ioo) a (fun z hz => htrace z hz.1) hx.2.2.2
    filter_upwards [hgood] with Γ hΓ
    filter_upwards [hΓ] with θ hθ
    exact fun t ht => hθ k t ht
  have hall : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ x : S, ∀ k : ℕ,
      volume ((a ∘ Γ.val.1) ''
        ((Γ.val.1 ⁻¹' Free) ∩ (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩
          Γ.val.1 ⁻¹' V x.val))) = 0 :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr (hlocal x)
  filter_upwards [hall] with Γ hΓ
  intro k
  apply measure_mono_null (t := {a (π OnePoint.infty)} ∪ ⋃ x : S,
    (a ∘ Γ.val.1) '' ((Γ.val.1 ⁻¹' Free) ∩
      (Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Γ.val.1 ⁻¹' V x.val)))
  · rintro _ ⟨y, ⟨⟨t, ht, rfl⟩, hy⟩, rfl⟩
    by_cases heq : Γ.val.1 t = π OnePoint.infty
    · exact Or.inl (by simpa only [heq] using mem_singleton (a (π OnePoint.infty)))
    · obtain ⟨x, hx, htx⟩ := mem_iUnion₂.mp (hcover ⟨hy, heq⟩)
      exact Or.inr (mem_iUnion.mpr ⟨⟨x, hx⟩, t, ⟨hy, ht, htx⟩, rfl⟩)
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null fun x => hΓ x k)


theorem ranked_ae_code_real_free_level_incidence_null
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f d.quotientDomain)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), volume
      {θ | ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i} = 0 := by
  let Free := d.quotientDomainᶜ \ Flags
  let w : Sphere → UnitAddCircle := fun x => (realBoundaryTrace d.quotientDomain f x : UnitAddCircle)
  have hzero (x : Sphere) (hx : x ∈ Free) :
      limsup f (𝓝[d.quotientDomain] x) - liminf f (𝓝[d.quotientDomain] x) ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp (le_zero_iff.mp ((hband x hx.1).trans_eq (hmFree x hx)))
  have htrace : ∀ x ∈ Free, ∀ t, (t, x) ∈ d.levels i ↔ w x = t := by
    intro x hx t
    rw [hlevel]
    exact circleBandGraph_of_trace hM (by rw [hdense.closure_eq]; exact mem_univ x)
      (tendsto_boundaryTrace_of_zero_band hM
        (by rw [hdense.closure_eq]; exact mem_univ x) (hzero x hx))
  have htags := ranked_ae_code_real_band_tag_trace_null rank hrank hsard hsch d hG hU hdense π hπ
    hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    (d.levelWeights i) hm hweight hvisits hband hmFree hH hP hunique ω hτ i hlevel
  apply ae_code_free_level_incidence_null d P i Free
    (fun x hx => hdust.symm ▸ hx.1) w htrace hm hweight hvisits hcover
    (fun n => disjoint_left.mpr fun x hx hp => hx.2 (hdeletions n hp))
  filter_upwards [htags] with Γ hΓ
  intro k
  simpa only [w, image_image, Function.comp_def] using volume_addCircle_image_eq_zero (hΓ k)


theorem ranked_mean_code_real_level_intersections_finite
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f d.quotientDomain)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ d.physicalDomain → f (π OnePoint.infty) = 0)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    (∫⁻ θ : UnitAddCircle, ∫⁻ Γ : BasePathCode d,
      pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1 ∂(P : Measure _)) < ∞ := by
  have hfree := ranked_ae_code_real_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ hlevel
  have hfinite : ∀ᵐ γ ∂(codePathLaw d P : Measure C(PathTime, Sphere)),
      physicalDomainLength d.domainEquiv d.basePoint γ < ∞ := by
    change ∀ᵐ γ ∂(P : Measure (BasePathCode d)).map (codePath d), _
    apply (ae_map_iff (measurable_codePath d).aemeasurable
      (measurableSet_finitePhysicalDomainLength d.domainEquiv hU d.basePoint)).mpr
    exact Eventually.of_forall fun Γ => Γ.property.1.1
  have hdom := mean_real_domain_circle_count_finite hcoarea hG d.domainEquiv hU d.basePoint π hπ he
    f hf hv henergy hK hzero hinfty (codePathLaw d P) hfinite ρ hρ
    ((meanPhysicalOccupation_codePathLaw d hU P).trans hocc) hρ2
  have hvol : ∀ x ∈ Flags, volume {θ : UnitAddCircle | (θ, x) ∈ d.levels i} ≤ d.levelWeights i x := by
    intro x hx
    have heq : {θ : UnitAddCircle | (θ, x) ∈ d.levels i} =
        {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph d.quotientDomain f} :=
      Set.ext fun θ => hlevel θ x
    rw [heq]
    exact (volume_circleBandGraph_incidence_le_budget hM
      (by rw [hdense.closure_eq]; exact mem_univ x) le_rfl).trans (hband x (hFlagsB hx))
  have hflag := mean_flag_intersection_count_finite_of_support (hH i) Flags hFlags
    (d.levelWeights i) hvol (codePathLaw d P) hm hweight hvisits
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hb := mean_parameter_level_count_le_of_no_free_hits (hH i)
    d.quotientDomain Flags hσU hFlags P (codePath d) (measurable_codePath d) hfree'
  have hDmeas := measurable_sigmaCompact_restricted_relation_path_count hσU
    ((hH i).preimage continuous_swap)
  have hFmeas := measurable_flag_intersection_count (hH i) Flags hFlags
  have hdint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (d.quotientDomain ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hDmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  have hfint (θ : UnitAddCircle) :
      (∫⁻ Γ : BasePathCode d, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i})
        (codePath d Γ) ∂(P : Measure _)) =
      ∫⁻ γ, pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ
        ∂(codePathLaw d P : Measure _) := by
    have hmeas : Measurable (fun γ : C(PathTime, Sphere) =>
        pathImageCount (Flags ∩ {x | (θ, x) ∈ d.levels i}) γ) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    rw [codePathLaw, ProbabilityMeasure.toMeasure_map]
    exact (lintegral_map hmeas (measurable_codePath d)).symm
  apply hb.trans_lt
  apply ENNReal.add_lt_top.mpr
  constructor
  · simp_rw [hdint]
    simpa only [hlevel] using hdom
  · simpa only [hfint] using hflag


theorem ranked_code_real_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (f : Sphere → ℝ) {M : ℝ} (hM : ∀ z ∈ d.quotientDomain, |f z| ≤ M)
    (hf : ContinuousOn f d.quotientDomain)
    (hv : ContDiffOn ℝ 1 (fun z : ℂ => f (π (z : Sphere)))
      (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain))
    (henergy : (∫⁻ z in ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain,
      ENNReal.ofReal ‖fderiv ℝ (fun z : ℂ => f (π (z : Sphere))) z‖ ^ 2) < ∞)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ K → f (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ d.physicalDomain → f (π OnePoint.infty) = 0)
    (P : ProbabilityMeasure (BasePathCode d))
    (ρ : Sphere → ℝ≥0∞) (hρ : Measurable ρ)
    (hocc : meanCodeOccupation d P = sphericalArea.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂sphericalArea) < ∞)
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hband : ∀ z ∈ d.quotientDomainᶜ, ENNReal.ofReal
      (limsup f (𝓝[d.quotientDomain] z) - liminf f (𝓝[d.quotientDomain] z)) ≤
        d.levelWeights i z)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hlevel : ∀ θ x, (θ, x) ∈ d.levels i ↔ (x, θ) ∈ circleBandGraph d.quotientDomain f) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  have hmean := ranked_mean_code_real_level_intersections_finite rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy
    hK hzero hinfty P ρ hρ hocc hρ2 i hm hweight hvisits hband hmFree hcover hdeletions
    hH hP hunique ω hτ hlevel
  have hfree := ranked_ae_code_real_free_level_incidence_null rank hrank hsard hsch d hG hU hdense hdust
    π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB f hM hf hv henergy P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ hlevel
  have hσU : IsSigmaCompact d.quotientDomain := by
    let : LocallyCompactSpace d.quotientDomain := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  have hfree' : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ᵐ θ : UnitAddCircle ∂volume,
      ¬ ∃ x ∈ range (codePath d Γ) ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
    filter_upwards [hfree] with Γ hΓ
    exact ae_iff.mpr (by simpa only [not_not, codePath] using hΓ)
  have hdisj : Disjoint d.quotientDomain Flags :=
    disjoint_left.mpr fun x hx hxf => hFlagsB hxf hx
  simpa only [codePath] using ae_level_parameter_free_avoidance (hH i)
    d.quotientDomain Flags hσU hFlags hdisj P (codePath d) (measurable_codePath d) hfree' hmean

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalRealCodeLevels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real seed coordinates retain the same code-law intersection estimates
when interspersed with masked period coordinates in an inherited order. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance localInst_r5b7c64_15 : BorelSpace Sphere := ⟨rfl⟩
theorem PhysicalRealCoordinate.ranked_code_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (Q : PhysicalRealCoordinate d π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = circleBandGraph d.quotientDomain Q.quotient)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight)
    {K : Set ℂ} (hK : IsCompact K)
    (hzero : ∀ z : ℂ, (z : Sphere) ∈ d.physicalDomain → z ∉ K → Q.quotient (π (z : Sphere)) = 0)
    (hinfty : OnePoint.infty ∈ d.physicalDomain → Q.quotient (π OnePoint.infty) = 0) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  let D := ((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain
  let e := Complex.equivRealProdCLM
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hDc : D = e ⁻¹' realChartDomain d.physicalDomain := by
    ext z
    change (z : Sphere) ∈ d.physicalDomain ↔ (e.symm (e z) : Sphere) ∈ d.physicalDomain
    rw [e.symm_apply_apply]
  have hreal : IsOpen (realChartDomain d.physicalDomain) :=
    hG.preimage (OnePoint.continuous_coe.comp e.symm.continuous)
  have hs : ContDiffOn ℝ 1 Q.physical (realChartDomain d.physicalDomain) :=
    Q.physical_smooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hpc : ContDiffOn ℝ 1 (Q.physical ∘ e) D := by
    rw [hDc]
    exact hs.comp e.contDiff.contDiffOn (fun _ hx => hx)
  have heq : EqOn (fun z : ℂ => Q.quotient (π (z : Sphere))) (Q.physical ∘ e) D :=
    fun z hz => (Q.pullback z hz).symm
  have hv := hpc.congr heq
  have hEn : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2)) < ∞ := by
    rw [hDc]
    exact complex_chart_differential_energy_finite hreal hs Q.physical_energy
  have henergy : (∫⁻ z in D, ENNReal.ofReal
      ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) < ∞ := by
    have heD : ∀ᵐ z ∂volume.restrict D,
        fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z =
          fderiv ℝ (Q.physical ∘ e) z := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
      have hev : (fun y : ℂ => Q.quotient (π (y : Sphere))) =ᶠ[𝓝 z] Q.physical ∘ e :=
        Filter.mem_of_superset (hD.mem_nhds hz) (fun _ hy => heq hy)
      exact hev.fderiv_eq
    have heD' : (∫⁻ z in D, ENNReal.ofReal
        ‖fderiv ℝ (fun z : ℂ => Q.quotient (π (z : Sphere))) z‖ ^ 2) =
        ∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ (Q.physical ∘ e) z‖ ^ 2 := by
      apply lintegral_congr_ae
      filter_upwards [heD] with z hz
      rw [hz]
    rw [heD']
    simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hEn
  have hbound (x : Sphere) (_ : x ∈ d.quotientDomain) : |Q.quotient x| ≤ 1 := by
    rw [abs_of_nonneg (Q.quotient_unit x).1]
    exact (Q.quotient_unit x).2
  have hband (x : Sphere) (hx : x ∈ d.quotientDomainᶜ) :
      ENNReal.ofReal (limsup Q.quotient (𝓝[d.quotientDomain] x) -
        liminf Q.quotient (𝓝[d.quotientDomain] x)) ≤ d.levelWeights i x := by
    have hcl : x ∈ closure d.quotientDomain := by rw [hdense.closure_eq]; trivial
    let : NeBot (𝓝[d.quotientDomain] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hlo : 0 ≤ liminf Q.quotient (𝓝[d.quotientDomain] x) :=
      le_liminf_of_le (isBoundedUnder_of_eventually_le
        (Eventually.of_forall fun y => (Q.quotient_unit y).2)).isCoboundedUnder_ge
        (Eventually.of_forall fun y => (Q.quotient_unit y).1)
    have hhi : limsup Q.quotient (𝓝[d.quotientDomain] x) ≤ 1 :=
      limsup_le_of_le (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun y => (Q.quotient_unit y).1)).isCoboundedUnder_le
        (Eventually.of_forall fun y => (Q.quotient_unit y).2)
    have hxB : x ∈ d.dust := hdust.symm ▸ hx
    rw [hweights, MaskedCoordinateData.dustWeight, dite_eq_left hxB]
    apply band_width_le_of_fiber_subset hbound hcl (by linarith)
    intro θ hθ
    apply C.marked_fiber ⟨x, hxB⟩
    rwa [hgraph]
  exact ranked_code_real_generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB
    Q.quotient hbound Q.quotient_continuous hv henergy hK hzero hinfty P ρ hρ hocc hρ2
    i hm hweight hvisits hband hmFree hcover hdeletions hH hP hunique ω hτ
    (fun θ x => by rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph])

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanBandWeight
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local branch widths are controlled by the actual masked-coordinate
weights. Exact Haar length prevents a change of branch from weakening
the weight used by subsequent code laws. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_22
theorem SmoothMeanPeriodData.branch_width_le_dustWeight
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M B : Set Sphere} (hdense : Dense U) {b : Sphere} {π : Sphere → Sphere}
    (hbS : b ∉ S) (hBU : B ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F G U S M b π)
    (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hgraph : C.graph = periodBandGraph U M b Q.patch Q.branch)
    (i : Q.Index) {x : Sphere} (hx : x ∈ B ∩ M) (hxi : x ∈ Q.patch i) :
    ENNReal.ofReal (limsup (Q.branch i) (𝓝[U] x) -
      liminf (Q.branch i) (𝓝[U] x)) ≤ C.dustWeight x := by
  have hwidth : limsup (Q.branch i) (𝓝[U] x) -
      liminf (Q.branch i) (𝓝[U] x) ≤ 1 :=
    (Q.branch_width_le_hit hsch hsep A K hK hKS η F f hf hmap hdense h0 h1 hF i
      ⟨hx.2, hBU hx.1⟩ hxi).trans measureReal_le_one
  have hcompat : ∀ i j y, y ∈ Q.patch i → y ∈ Q.patch j → ∀ θ,
      (y, θ) ∈ circleBandGraph U (Q.branch i) ↔
        (y, θ) ∈ circleBandGraph U (Q.branch j) := by
    intro i j y hyi hyj θ
    obtain ⟨k, hk⟩ := Q.transition i j y hyi hyj
    exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hk) θ).symm
  have hsub : {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph U (Q.branch i)} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (C.lower ⟨x, hx.1⟩) (C.upper ⟨x, hx.1⟩) := by
    intro θ hθ
    apply C.marked_fiber ⟨x, hx.1⟩
    rw [hgraph]
    exact (periodBandGraph_on_patch U M b Q.patch Q.branch
      (fun j hj => hbS (Q.patch_closure j (subset_closure hj))) hcompat hxi θ).mpr ⟨hx.2, hθ⟩
  simpa only [MaskedCoordinateData.dustWeight, dite_eq_left hx.1] using
    band_width_le_of_fiber_subset (fun y _ => Q.bounded i y)
      (show x ∈ closure U by rw [hdense.closure_eq]; trivial) hwidth hsub

 omit [MeasurableSpace C(PathTime, Sphere)] in
 theorem masked_singular_weight_ge_one
    {G U M B : Set Sphere} {b : Sphere} {π : Sphere → Sphere}
    {I : Type*} (patch : I → Set Sphere) (branch : I → Sphere → ℝ)
    (C : MaskedCoordinateData G U π (fun x : B => x.val))
    (hgraph : C.graph = periodBandGraph U M b patch branch)
    (hb : b ∈ B) (hbM : b ∈ M) : 1 ≤ C.dustWeight b := by
  have hsub : (univ : Set UnitAddCircle) ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc (C.lower ⟨b, hb⟩) (C.upper ⟨b, hb⟩) := by
    intro θ _
    apply C.marked_fiber ⟨b, hb⟩
    rw [hgraph]
    exact periodBandGraph_singular U M b patch branch hbM θ
  have h := (measure_mono (μ := (volume : Measure UnitAddCircle)) hsub).trans
    ((volume_addCircle_image_Icc_le _ _).trans
      (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  simpa only [MaskedCoordinateData.dustWeight, dite_eq_left hb, AddCircle.measure_univ, ENNReal.ofReal_one] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SmoothMeanCodeLevels
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generic prior levels for the actual smoothed mean and its masked
coordinate. The atlas and its weight estimates are derived from that
coordinate, not supplied as a generic-intersection hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_23
theorem SmoothMeanPeriodData.ranked_code_generic_levels
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (hsep : UnitDiskCrosscutSeparation)
    (S M : Set Sphere) (hS : IsOpen S) (hM : IsClosed M)
    (hinftyM : π OnePoint.infty ∉ M)
    (hboundary : M \ interior M ⊆ d.quotientDomain)
    (b : Sphere) (hb : b ∈ Flags) (hbM : b ∈ M) (hbS : b ∉ S)
    (hMS : M \ {b} ⊆ S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ d.quotientDomain, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map (f := f) (hf.aemeasurable)) F
      d.physicalDomain d.quotientDomain S M b π)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (hgraph : C.graph = periodBandGraph d.quotientDomain M b Q.patch Q.branch)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  let : Countable Q.Index := Q.countableIndex
  let w : Sphere → UnitAddCircle := fun x =>
    diskMeanCircle hsch K hKS (η.map (f := f) (hf.aemeasurable)) (F x) + (Q.error x : UnitAddCircle)
  have hmiss (j : Q.Index) : b ∉ Q.patch j :=
    fun hj => hbS (Q.patch_closure j (subset_closure hj))
  have hcompat : ∀ j k x, x ∈ Q.patch j → x ∈ Q.patch k → ∀ θ,
      (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch j) ↔
        (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch k) := by
    intro j k x hj hk θ
    obtain ⟨m, hm⟩ := Q.transition j k x hj hk
    exact (Set.ext_iff.mp (circleBand_fiber_eq_of_eventually_add_int hm) θ).symm
  have hlocal (j : Q.Index) (x : Sphere) (hx : x ∈ M ∩ Q.patch j) (θ : UnitAddCircle) :
      (x, θ) ∈ circleBandGraph d.quotientDomain (Q.branch j) ↔
        (θ, x) ∈ d.levels i := by
    rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph,
      periodBandGraph_on_patch _ _ _ _ _ hmiss hcompat hx.2]
    exact (and_iff_right hx.1).symm
  have hband (j : Q.Index) (x : Sphere)
      (hx : x ∈ (d.quotientDomainᶜ ∩ M) ∩ Q.patch j) :
      ENNReal.ofReal (limsup (Q.branch j) (𝓝[d.quotientDomain] x) -
        liminf (Q.branch j) (𝓝[d.quotientDomain] x)) ≤ d.levelWeights i x := by
    rw [hweights]
    exact Q.branch_width_le_dustWeight hsch hsep A K hK hKS η F f hf hmap hdense hbS
      (by rw [hdust]) h0 hstrict hF C hgraph j ⟨hdust.symm ▸ hx.1.1, hx.1.2⟩ hx.2
  have hw (j : Q.Index) (x : Sphere) (hx : x ∈ d.quotientDomain ∩ Q.patch j) :
      (Q.branch j x : UnitAddCircle) = w x := by
    have hxS := Q.patch_closure j (subset_closure hx.2)
    dsimp only [w]
    rw [Q.branch_value j x hx.2, AddCircle.coe_add]
    congr 1
    rw [← diskMeanCircle_projection hsch hsep K hK hKS (η.map (f := f) (hf.aemeasurable)),
      upperHalfPlaneClamp_val (logarithmicCutChart_nonneg (Q.angle j) (h1 x hxS)),
      logarithmicCutChart_projection (Q.angle j) (h0 x hxS)]
  exact (ranked_code_period_generic_levels rank hrank hcoarea hsard hsch d
    hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
    i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
    Q.patch Q.patch_open M hM hinftyM hboundary b hb
    (by
      rw [hweights]
      exact masked_singular_weight_ge_one Q.patch Q.branch C hgraph
        (hdust.symm ▸ hFlagsB hb) hbM)
    (fun θ x hx => by
      rw [hlevel, mem_preimage, Prod.swap_prod_mk, hgraph] at hx
      exact hx.1)
    (hMS.trans Q.cover) Q.branch Q.bound (fun j x _ => Q.bounded j x)
    Q.continuous Q.branch_smooth Q.branch_energy hband hlocal w hw
    (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S)
    ((hG.preimage OnePoint.continuous_coe).inter
      (hS.preimage (hπ.comp OnePoint.continuous_coe)))
    (fun _ hz => hz.1)
    (fun z hzG hzM => ⟨hzG, hMS ⟨hzM, fun heq => hFlagsB hb (heq ▸
      (show π (z : Sphere) ∈ d.quotientDomain from
        (he ⟨z, hzG⟩) ▸ (d.domainEquiv ⟨z, hzG⟩).property))⟩⟩)
    Q.physical Q.physical_smooth
    (fun z hz => Q.physical_value z hz.1 hz.2) Q.physical_energy).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SelectedLevelPresentation
attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations of selected real and mean coordinates, retaining
their functions, compact laws, and the data for subsequent code-law bounds. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)]


variable [BorelSpace C(PathTime, Sphere)]

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_24
theorem SelectedLevelPresentation.generic_levels_oai
    {L : Type*} [LinearOrder L] (rank : ℕ → L) (hrank : Injective rank)
    (hcoarea : PlanarLipschitzFiberCoarea)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
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
    (i : ℕ) (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) => d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm
      (fun x : support (d.levelWeights i) => meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hmFree : ∀ z ∈ d.quotientDomainᶜ \ Flags, d.levelWeights i z = 0)
    (hdeleteCover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdeletions : ∀ n, (d.flagDeletions n : Set Sphere) ⊆ Flags)
    (hH : ∀ j, IsClosed (d.levels j))
    (hP : RankedLevelNullCompatibility rank d.levels (d.quotientDomainᶜ \ Flags))
    (hunique : ∀ x ∈ d.quotientDomainᶜ \ Flags, ∀ j a b,
      (a, x) ∈ d.levels j → (b, x) ∈ d.levels j → a = b)
    (ω : TupleType → ℝ≥0∞) [SFinite (tupleReference ω)]
    (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (hsep : UnitDiskCrosscutSeparation)
    (C : MaskedCoordinateData d.physicalDomain d.quotientDomain π
      (fun x : d.dust => x.val))
    (R : SelectedLevelPresentation hsch d π C)
    (hlevel : d.levels i = Prod.swap ⁻¹' C.graph)
    (hweights : d.levelWeights i = C.dustWeight)
    (hsingular : (C.singular : Sphere) ∈ Flags) :
    ∀ᵐ θ : UnitAddCircle ∂volume,
      (∫⁻ Γ : BasePathCode d, pathImageCount {x | (θ, x) ∈ d.levels i} Γ.val.1
        ∂(P : Measure _)) < ∞ ∧
      ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
        ¬ ∃ x ∈ range Γ.val.1 ∩ (d.quotientDomainᶜ \ Flags), (θ, x) ∈ d.levels i := by
  cases R with
  | inl Q =>
      exact Q.coordinate.ranked_code_generic_levels rank hrank hcoarea hsard hsch d
        hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
        i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
        C Q.graph_eq hlevel hweights Q.isCompact_support Q.zero_off Q.zero_infty
  | inr Q =>
      exact Q.mean.ranked_code_generic_levels rank hrank hcoarea hsard hsch d
        hG hU hdense hdust π hπ hclosed hsurj hr he hTD hbad Flags hFlags hFlagsB P ρ hρ hocc hρ2
        i hm hweight hvisits hmFree hdeleteCover hdeletions hH hP hunique ω hτ
        Q.arcs Q.diskArcs Q.compact_diskArcs Q.terminal_diskArcs Q.law Q.map Q.arcMap
        Q.measurable_arcMap Q.arcMap_eq hsep Q.neighborhood Q.mask Q.open_neighborhood
        Q.closed_mask Q.excludes_infty Q.boundary_domain Q.singular (Q.singular_eq ▸ hsingular)
        Q.singular_mask Q.singular_outside Q.punctured_mask Q.nonzero Q.unit_bound Q.strict_bound
        Q.injective_arcs C Q.graph_eq hlevel hweights

end CircleDomainRigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels_oai.{u_1} := @OAI.CircleDomainRigidity.SelectedLevelPresentation.generic_levels_oai.{u_1}
