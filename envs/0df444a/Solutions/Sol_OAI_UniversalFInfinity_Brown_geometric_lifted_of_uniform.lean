-- Prove2me | solution 1 for OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:57:03.938612+00:00
-- url     : https://prove2.me/submissions/82f38f4a-3003-41d8-8f97-c31bc262914b

import Mathlib
import Definitions.Def_UniversalFInfinity
import Definitions.Def_OAIQWUFI008
import Theorems.Thm_OAI_UniversalFInfinity_Cellular_contractible_of_sphereFillable

section
-- module Solutions.OAIQW_UniversalFInfinity.TopologicalTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TopologicalTower
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

lemma tailLift_of {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (g : ∀ m, n ≤ m → C(X m,Y))
    (hg : ∀ i j (hi : n ≤ i) (hij : i ≤ j) x,
      g i hi x = g j (hi.trans hij) (f i j hij x))
    (m : ℕ) (hm : n ≤ m) (x : X m) :
    tailLift X f hf n g hg (of X f m x) = g m hm x := by
  change g (max n m) _ (f m (max n m) _ x) = g m hm x
  exact (hg m (max n m) hm (le_max_right _ _) x).symm

variable (hext : ExtendsReals X f)

omit [DirectedSystem X (f · · ·)] in
lemma realExtension_spec (n : ℕ) (g : C(X n,ℝ)) (x : X n) :
    realExtension X f hext n g (f n (n+1) (Nat.le_succ n) x) = g x :=
  (hext n g).choose_spec x

omit [DirectedSystem X (f · · ·)] in
lemma realFamily_self (n : ℕ) (g : C(X n,ℝ)) : realFamily X f hext n g n le_rfl = g :=
  by simp only [realFamily,Nat.leRecOn_self]

lemma realFamily_compat (n : ℕ) (g : C(X n,ℝ)) (i j : ℕ) (hi : n ≤ i)
    (hij : i ≤ j) (x : X i) :
    realFamily X f hext n g i hi x =
      realFamily X f hext n g j (hi.trans hij) (f i j hij x) := by
  induction j,hij using Nat.le_induction with
  | base => rw [DirectedSystem.map_self']
  | succ j hij ih =>
    unfold realFamily
    rw [Nat.leRecOn_succ (hi.trans hij)]
    rw [← DirectedSystem.map_map' f hij (Nat.le_succ j),realExtension_spec]
    exact ih

include hf hext in
lemma exists_global_real_extension (n : ℕ) (g : C(X n,ℝ)) :
    ∃ G : C(Space X f,ℝ), ∀ x, G (of X f n x) = g x := by
  refine ⟨tailLift X f hf n (realFamily X f hext n g)
    (realFamily_compat X f hext n g),?_⟩
  intro x
  rw [tailLift_of X f hf n _ _ n le_rfl,realFamily_self]

include hf hext in
lemma t2Space (hsep : ∀ n (x y : X n), x ≠ y →
    ∃ g : C(X n,ℝ), g x ≠ g y) : T2Space (Space X f) := by
  constructor
  intro z w hzw
  obtain ⟨n,x,y,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f z w
  have hxy : x ≠ y := fun h => hzw (congrArg (of X f n) h)
  obtain ⟨g,hg⟩ := hsep n x y hxy
  obtain ⟨G,hG⟩ := exists_global_real_extension X f hf hext n g
  apply separated_by_continuous G.continuous
  change G (of X f n x) ≠ G (of X f n y)
  rw [hG,hG]
  exact hg

lemma range_mono {i j : ℕ} (h : i ≤ j) : Set.range (of X f i) ⊆ Set.range (of X f j) := by
  rintro _ ⟨x,rfl⟩
  exact ⟨f i j h x,of_compat X f i j h x⟩

variable [∀ n, T1Space (X n)]

include hf in
lemma selection_closed (x : ℕ → Space X f) (hx : ∀ n, x n ∉ Set.range (of X f n))
    (S : Set (Space X f)) (hS : S ⊆ Set.range x) : IsClosed S := by
  rw [isClosed_iff]
  intro m
  have hfin : (S ∩ Set.range (of X f m)).Finite := by
    apply ((Set.finite_Iio m).image x).subset
    rintro z ⟨hzS,hzm⟩
    obtain ⟨n,rfl⟩ := hS hzS
    refine ⟨n,?_,rfl⟩
    change n < m
    by_contra hnm
    exact hx n (range_mono X f (Nat.le_of_not_gt hnm) hzm)
  have hh := hfin.preimage (of_injective X f hf m).injOn
  rw [Set.preimage_inter,Set.preimage_range,Set.inter_univ] at hh
  exact hh.isClosed

include hf in

theorem compact_bounded {K : Set (Space X f)} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (of X f n) := by
  classical
  by_contra hn
  have hex : ∀ n, ∃ x ∈ K, x ∉ Set.range (of X f n) := by
    intro n
    exact Set.not_subset.mp (fun h => hn ⟨n,h⟩)
  choose x hxK hx using hex
  have hall : ∀ S ⊆ Set.range x, IsClosed S := selection_closed X f hf x hx
  have hcompact : IsCompact (Set.range x) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hxK)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hfinite := hcompact.finite hdiscrete
  have hex : ∀ z ∈ Set.range x, ∃ n, z ∈ Set.range (of X f n) := by
    intro z _
    obtain ⟨n,y,rfl⟩ := DirectLimit.exists_eq_mk f z
    exact ⟨n,y,rfl⟩
  choose idx hidx using hex
  let n := hfinite.toFinset.sup (fun z => if hz : z ∈ Set.range x then idx z hz else 0)
  have hbound : Set.range x ⊆ Set.range (of X f n) := by
    intro z hz
    apply range_mono X f (j := n) _ (hidx z hz)
    have hh := Finset.le_sup (f := fun z => if hz : z ∈ Set.range x then idx z hz else 0)
      (hfinite.mem_toFinset.mpr hz)
    simpa only [dite_eq_left hz] using hh
  exact hx n (hbound (Set.mem_range_self n))

end UniversalFInfinity.TopologicalTower

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.TowerCoverings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.TopologicalTower

section
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))
variable (k : ℕ) (U : ∀ n, k ≤ n → Set (X n))
variable (hU : ∀ i j (hi : k ≤ i) (hij : i ≤ j), f i j hij ⁻¹' U j (hi.trans hij) = U i hi)

include hf hU in
lemma preimage_tailSet (n : ℕ) (hn : k ≤ n) :
    of X f n ⁻¹' tailSet X f k U = U n hn := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,y,hy,hyx⟩ : ∃ j, ∃ (hj : k ≤ j), ∃ y ∈ U j hj,
        of X f j y = of X f n x := by simpa only [tailSet,Set.mem_preimage,Set.mem_iUnion,Set.mem_image] using hx
    let m := max j n
    have he : f j m (le_max_left _ _) y = f n m (le_max_right _ _) x :=
      of_injective X f hf m ((of_compat X f j m (le_max_left _ _) y).trans
        (hyx.trans (of_compat X f n m (le_max_right _ _) x).symm))
    have hym : f j m (le_max_left _ _) y ∈ U m (hj.trans (le_max_left _ _)) := by
      change y ∈ f j m (le_max_left _ _) ⁻¹' U m _
      rw [hU]
      exact hy
    rw [he] at hym
    change x ∈ f n m (le_max_right _ _) ⁻¹' U m _ at hym
    rw [hU] at hym
    exact hym
  · intro hx
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨hn,⟨x,hx,rfl⟩⟩⟩

include hf hU in
lemma tailSet_isOpen (hopen : ∀ n hn, IsOpen (U n hn)) : IsOpen (tailSet X f k U) := by
  change @IsOpen _ (TopologicalSpace.coinduced (fun x : Σ n, X n => of X f x.1 x.2) inferInstance) _
  rw [isOpen_coinduced,isOpen_sigma_iff]
  intro n
  change IsOpen (of X f n ⁻¹' tailSet X f k U)
  rcases le_total k n with hn | hn
  · rw [preimage_tailSet X f hf k U hU n hn]
    exact hopen n hn
  · have heq : of X f n = of X f k ∘ f n k hn := (funext (of_compat X f n k hn)).symm
    rw [heq,Set.preimage_comp,preimage_tailSet X f hf k U hU k le_rfl]
    exact (hopen k le_rfl).preimage (f n k hn).continuous

end

section
open Set Topology
universe u w
variable {G : Type w} [Group G]
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, MulAction G (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable [EquivariantSystem (G := G) X f]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

variable (hext : ExtendsSlices (G := G) X f)

omit [DirectedSystem X (f · · ·)] [EquivariantSystem (G := G) X f] in
lemma extendSlice_spec (n : ℕ) (U : Slice (G := G) X n) :
    f n (n+1) (Nat.le_succ n) ⁻¹' (extendSlice X f hext n U).carrier = U.carrier :=
  (hext n U).choose_spec

omit [DirectedSystem X (f · · ·)] [EquivariantSystem (G := G) X f] in
lemma sliceFamily_self (k : ℕ) (U : Slice (G := G) X k) : sliceFamily X f hext k U k le_rfl = U := by
  simp only [sliceFamily,Nat.leRecOn_self]

omit [EquivariantSystem (G := G) X f] in
lemma sliceFamily_compat (k : ℕ) (U : Slice (G := G) X k) (i j : ℕ)
    (hi : k ≤ i) (hij : i ≤ j) :
    f i j hij ⁻¹' (sliceFamily X f hext k U j (hi.trans hij)).carrier =
      (sliceFamily X f hext k U i hi).carrier := by
  induction j,hij using Nat.le_induction with
  | base => ext x; simp only [Set.mem_preimage,DirectedSystem.map_self']
  | succ j hij ih =>
    unfold sliceFamily
    rw [Nat.leRecOn_succ (hi.trans hij)]
    have hcomp : f i (j+1) (hij.trans (Nat.le_succ j)) =
        f j (j+1) (Nat.le_succ j) ∘ f i j hij := by
      ext x
      exact (DirectedSystem.map_map' f hij (Nat.le_succ j) x).symm
    change (f i (j+1) _) ⁻¹' (extendSlice X f hext j _).carrier = _
    rw [hcomp,Set.preimage_comp,extendSlice_spec]
    exact ih

include hf in
lemma tailSet_disjoint (k : ℕ) (U : ∀ n, k ≤ n → Set (X n))
    (hU : ∀ i j (hi : k ≤ i) (hij : i ≤ j), f i j hij ⁻¹' U j (hi.trans hij) = U i hi)
    (hd : ∀ n hn (g : G), ((g • ·) '' U n hn ∩ U n hn).Nonempty → g = 1) :
    ∀ g : G, ((g • ·) '' tailSet X f k U ∩ tailSet X f k U).Nonempty → g = 1 := by
  intro g hg
  obtain ⟨_,⟨z,hz,rfl⟩,hgz⟩ := hg
  obtain ⟨j,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  let m := max k j
  have he : of X f j x = of X f m (f j m (le_max_right _ _) x) :=
    (of_compat X f j m (le_max_right _ _) x).symm
  change of X f j x ∈ tailSet X f k U at hz
  rw [he] at hz
  change of X f m _ ∈ tailSet X f k U at hz
  have hmz := (Set.ext_iff.mp (preimage_tailSet X f hf k U hU m (le_max_left _ _)) _).mp hz
  change g • of X f j x ∈ tailSet X f k U at hgz
  rw [he,smul_of] at hgz
  have hmgz := (Set.ext_iff.mp (preimage_tailSet X f hf k U hU m (le_max_left _ _)) _).mp hgz
  exact hd m (le_max_left _ _) g ⟨_,⟨_,hmz,rfl⟩,hmgz⟩

include hf hext in
lemma exists_disjoint_nhds
    (hstage : ∀ n (x : X n), ∃ U ∈ 𝓝 x,
      ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∀ z : Space X f, ∃ U ∈ 𝓝 z, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  intro z
  obtain ⟨k,x,rfl⟩ := DirectLimit.exists_eq_mk f z
  obtain ⟨U,hUx,hU⟩ := hstage k x
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUx
  let S : Slice (G := G) X k := ⟨V,hV,fun g hg => hU g
    (hg.mono (Set.inter_subset_inter (Set.image_mono hVU) hVU))⟩
  let W := fun n hn => (sliceFamily X f hext k S n hn).carrier
  have hW := sliceFamily_compat X f hext k S
  refine ⟨tailSet X f k W,?_,tailSet_disjoint X f hf k W hW
    (fun n hn => (sliceFamily X f hext k S n hn).disjoint)⟩
  apply (tailSet_isOpen X f hf k W hW (fun n hn => (sliceFamily X f hext k S n hn).isOpen)).mem_nhds
  change of X f k x ∈ tailSet X f k W
  have hw : x ∈ W k le_rfl := by simpa only [W,sliceFamily_self] using hxV
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨le_rfl,⟨x,hw,rfl⟩⟩⟩

end

section
open Set Topology
universe u v w
variable {G : Type w} [Group G]
variable (E : ℕ → Type u) [∀ n, TopologicalSpace (E n)] [∀ n, MulAction G (E n)]
variable (e : ∀ i j, i ≤ j → C(E i,E j)) [DirectedSystem E (e · · ·)]
variable [EquivariantSystem (G := G) E e] [∀ n, ContinuousConstSMul G (E n)]
variable (X : ℕ → Type v) [∀ n, TopologicalSpace (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (p : ∀ n, C(E n,X n))
variable (hp : ∀ i j h x, p j (e i j h x) = f i j h (p i x))

omit [EquivariantSystem (G := G) E e] [∀ n, ContinuousConstSMul G (E n)] in
lemma limitMap_isQuotient (hq : ∀ n, IsQuotientMap (p n)) :
    IsQuotientMap (limitMap E e X f p hp) := by
  refine ⟨?_,?_⟩
  · rw [isCoinducing_iff]
    intro U
    constructor
    · intro hU
      change @IsOpen _ (TopologicalSpace.coinduced (fun z : Σ n, X n => of X f z.1 z.2)
        inferInstance) U
      rw [isOpen_coinduced,isOpen_sigma_iff]
      intro n
      apply (hq n).isOpen_preimage.mp
      exact hU.preimage (continuous_of E e n)
    · exact fun hU => hU.preimage (limitMap E e X f p hp).continuous
  · intro z
    obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f z
    obtain ⟨y,rfl⟩ := (hq n).surjective x
    exact ⟨of E e n y,rfl⟩

omit [∀ n, ContinuousConstSMul G (E n)] in
lemma limitMap_fibers (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    (hq : ∀ n, IsQuotientCoveringMap (p n) G) (x y : Space E e) :
    limitMap E e X f p hp x = limitMap E e X f p hp y ↔ x ∈ MulAction.orbit G y := by
  obtain ⟨i,x,rfl⟩ := DirectLimit.exists_eq_mk e x
  obtain ⟨j,y,rfl⟩ := DirectLimit.exists_eq_mk e y
  let n := max i j
  change limitMap E e X f p hp (of E e i x) = limitMap E e X f p hp (of E e j y) ↔
    of E e i x ∈ MulAction.orbit G (of E e j y)
  rw [← of_compat E e i n (le_max_left _ _) x,← of_compat E e j n (le_max_right _ _) y]
  simp only [limitMap_of]
  constructor
  · intro hh
    have hh' := of_injective X f hf n hh
    obtain ⟨g,hg⟩ := (hq n).apply_eq_iff_mem_orbit.mp hh'
    exact ⟨g,congrArg (of E e n) hg⟩
  · rintro ⟨g,hg⟩
    have hh := congrArg (limitMap E e X f p hp) hg
    simpa only [smul_of,limitMap_of,(hq n).map_smul] using hh.symm

lemma limitMap_isQuotientCovering
    (he : ∀ i j h, IsClosedEmbedding (e i j h))
    (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    (hq : ∀ n, IsQuotientCoveringMap (p n) G)
    (hext : ExtendsSlices (G := G) E e) :
    IsQuotientCoveringMap (limitMap E e X f p hp) G where
  __ := limitMap_isQuotient E e X f p hp (fun n => (hq n).toIsQuotientMap)
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := limitMap_fibers E e X f p hp hf hq _ _
  disjoint := exists_disjoint_nhds E e he hext (fun n => (hq n).disjoint)

end

open Set Metric Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)] [∀ n, T1Space (X n)]
variable (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
variable (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma compactMap_factors {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : C(A,Space X f)) :
    ∃ (n : ℕ) (a : C(A,X n)), ∀ x, of X f n (a x) = g x := by
  obtain ⟨n,hn⟩ := compact_bounded X f hf (isCompact_range g.continuous)
  have hex (x : A) : ∃ y, of X f n y = g x := hn (Set.mem_range_self x)
  choose a ha using hex
  have hcont : Continuous a := by
    apply (of_closedEmbedding X f hf n).isEmbedding.continuous_iff.mpr
    have heq : of X f n ∘ a = g := funext ha
    rw [heq]
    exact g.continuous
  exact ⟨n,⟨a,hcont⟩,ha⟩

include hf in
lemma sphereFillable (hfill : EventuallyFills X f) : Cellular.SphereFillable (Space X f) := by
  intro n a
  obtain ⟨k,a',ha'⟩ := compactMap_factors X f hf a
  obtain ⟨j,hkj,b,hb⟩ := hfill n k a'
  refine ⟨⟨of X f j ∘ b,(continuous_of X f j).comp b.continuous⟩,?_⟩
  intro x
  change of X f j (b (Cellular.boundary n x)) = a x
  rw [hb,of_compat,ha']

include hf in

lemma contractible [T2Space (Space X f)] [Nonempty (Space X f)]
    [CWComplex (Set.univ : Set (Space X f))] (hfill : EventuallyFills X f) :
    ContractibleSpace (Space X f) :=
  Cellular.contractible_of_sphereFillable (sphereFillable X f hf hfill)

end UniversalFInfinity.TopologicalTower

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.BrownConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Brown

section
open Set Metric Topology Cellular Attachment
universe u

attribute [instance] Stage.topE Stage.topB Stage.nonemptyE Stage.nonemptyB
  Stage.cwE Stage.cwB Stage.action Stage.continuousAction Stage.orbitFinite Stage.finiteB

end

section
open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)
variable {n : ℕ} (S : Stage G n)

lemma nextE_extendsReal (f : C(S.E,ℝ)) : ∃ F : C((nextStage hunif S).E,ℝ),
    ∀ x,F (nextInE hunif S x) = f x := exists_real_extension _ f
lemma nextB_extendsReal (f : C(S.B,ℝ)) : ∃ F : C((nextStage hunif S).B,ℝ),
    ∀ x,F (nextInB hunif S x) = f x := exists_real_extension _ f
lemma nextE_extendsSlice (U : Set S.E) (hU : IsOpen U)
    (hd : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∃ V : Set (nextStage hunif S).E, IsOpen V ∧ (nextInE hunif S) ⁻¹' V = U ∧
      ∀ g : G,((g • ·) '' V ∩ V).Nonempty → g = 1 :=
  ⟨thickening _ U,thickening_isOpen _ hU,rfl,
    thickening_disjoint _ (equivariantFamily_smul (attaching hunif S)) hd⟩
end

open Set Metric Topology Cellular Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

lemma e_extendsReal : TopologicalTower.ExtendsReals (E hunif) (eMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextE_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [eMap, Sequential.map_step]
  exact hextension point
lemma b_extendsReal : TopologicalTower.ExtendsReals (B hunif) (bMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextB_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [bMap, Sequential.map_step]
  exact hextension point
instance totalT2 : T2Space (Total hunif) :=
  TopologicalTower.t2Space _ _ (eMap_closed hunif) (e_extendsReal hunif) (fun n => (stages hunif n).sepE)
instance baseT2 : T2Space (Base hunif) :=
  TopologicalTower.t2Space _ _ (bMap_closed hunif) (b_extendsReal hunif) (fun n => (stages hunif n).sepB)
lemma base_finite (n : ℕ) : Finite ((baseCW hunif).cell n) :=
  (stages hunif n).finiteB n

lemma eventually_fills : TopologicalTower.EventuallyFills (E hunif) (eMap hunif) := by
  intro n k a
  let j := max n k
  obtain ⟨F,hF⟩ := (stages hunif j).fill n (le_max_left n k)
    ((eMap hunif k j (le_max_right n k)).comp a)
  exact ⟨j,le_max_right n k,F,hF⟩
instance totalContractible : ContractibleSpace (Total hunif) :=
  TopologicalTower.contractible _ _ (eMap_closed hunif) (eventually_fills hunif)

lemma e_extendsSlices : TopologicalTower.ExtendsSlices (G := G) (E hunif) (eMap hunif) := by
  intro n U
  obtain ⟨V,hV,hpre,hdis⟩ := nextE_extendsSlice hunif (stages hunif n) U.carrier U.isOpen U.disjoint
  refine ⟨⟨V,hV,hdis⟩,?_⟩
  rw [eMap, Sequential.map_step]
  exact hpre

lemma pLimit_covering : IsQuotientCoveringMap (pLimit hunif) G :=
  TopologicalTower.limitMap_isQuotientCovering _ _ _ _ (pStage hunif) (p_compat hunif)
    (eMap_closed hunif) (bMap_closed hunif) (fun n => (stages hunif n).covering) (e_extendsSlices hunif)

instance baseConnected : ConnectedSpace (Base hunif) :=
  (pLimit_covering hunif).surjective.connectedSpace (pLimit hunif).continuous

end UniversalFInfinity.Brown

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalFInfinity.UniverseTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

open Set Metric Topology
namespace UniversalFInfinity.UniverseTransport

open Set Topology
universe u v
variable {G X E : Type u} [Group G] [TopologicalSpace X] [TopologicalSpace E]
  [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)

include hp in
lemma liftedCover_quotient : IsQuotientCoveringMap (liftedCover.{u,v} (p := p)) G where
  __ := (Homeomorph.ulift.symm.isQuotientMap.comp hp.toIsQuotientMap).comp
    Homeomorph.ulift.isQuotientMap
  continuous_const_smul g := by
    change Continuous (fun e : ULift.{v} E => ULift.up (g • e.down))
    exact continuous_uliftUp.comp ((hp.continuous_const_smul g).comp continuous_uliftDown)
  apply_eq_iff_mem_orbit := by
    intro e₁ e₂
    change ULift.up (p e₁.down) = ULift.up (p e₂.down) ↔ e₁ ∈ MulAction.orbit G e₂
    rw [ULift.up_inj,hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨g,ULift.down_injective hg⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,congrArg ULift.down hg⟩
  disjoint e := by
    obtain ⟨U,hU,hd⟩ := hp.disjoint e.down
    refine ⟨ULift.down ⁻¹' U,continuous_uliftDown.continuousAt.preimage_mem_nhds hU,?_⟩
    rintro g ⟨z,⟨y,hy,hyz⟩,hz⟩
    exact hd g ⟨z.down,⟨y.down,hy,congrArg ULift.down hyz⟩,hz⟩
end UniversalFInfinity.UniverseTransport
namespace UniversalFInfinity.Brown
open Set Topology UniverseTransport
universe z
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

include hunif in

theorem geometric_lifted_of_uniform_oai : HasTypeFInfinity (ULift.{z} G) := by
  let : T2Space (ULift.{z} (Base hunif)) := Homeomorph.ulift.symm.t2Space
  let : ContractibleSpace (ULift.{z} (Total hunif)) := Homeomorph.ulift.contractibleSpace
  let q : ULift.{z} (Total hunif) → ULift.{z} (Base hunif) :=
    liftedCover (p := pLimit hunif)
  have hq : IsQuotientCoveringMap q G := liftedCover_quotient (pLimit_covering hunif)
  let : ConnectedSpace (ULift.{z} (Base hunif)) := hq.surjective.connectedSpace hq.continuous
  let cw : CWComplex (univ : Set (ULift.{z} (Base hunif))) := liftCW
  refine ⟨ULift.{z} (Base hunif),inferInstance,inferInstance,inferInstance,cw,?_,?_,?_⟩
  · intro n
    change Finite (ULift.{z} ((baseCW hunif).cell n))
    have := base_finite hunif n
    infer_instance
  · let e : ULift.{z} (Total hunif) := Classical.choice inferInstance
    exact ⟨q e,⟨(hq.fundamentalGroupEquiv ⟨e,rfl⟩).trans
      ((MulEquiv.inv' G).symm.trans MulEquiv.ulift.symm)⟩⟩
  · exact ⟨ULift.{z} (Total hunif),inferInstance,inferInstance,q,hq.surjective,hq.isCoveringMap⟩
end UniversalFInfinity.Brown

end

end OAI
end

theorem solution.{z} : type_of% @OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform_oai.{z} := @OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform_oai.{z}
