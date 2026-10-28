-- Prove2me | solution 1 for OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:00:07.39292+00:00
-- url     : https://prove2.me/submissions/70702cda-e7dd-4bc1-99e2-717aac3f463e

import Mathlib
import Definitions.Def_SimpleOvergroups
import Definitions.Def_OAIQ66So016
import Definitions.Def_OAIQ66So030
import Definitions.Def_OAIQ66So031
import Theorems.Thm_OAI_OrderBrown_vanishing
import Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_localGroup_finitelyPresented
import Theorems.Thm_OAI_TwistedBrin_Basis_CutBasis_lower_exactSet
import Theorems.Thm_OAI_TwistedBrin_Basis_pair_regular_products

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimit
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SequentialCoreTower
section
open Set Topology
universe u v w
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

lemma core_covering [DiscreteTopology Q] :
    IsCoveringMap (core X f I δ Z pot hBase hPot hCoord).proj := FiberBundle.isCoveringMap

end

open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

lemma coverIncl_range (n : ℕ) :
    range (coverIncl X f I δ Z pot hBase hPot hCoord n) =
      (core X f I δ Z pot hBase hPot hCoord).proj ⁻¹' range (SequentialColimit.incl X f n) := by
  ext e
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(Z n).proj a,rfl⟩
  · rintro ⟨x,hx⟩
    obtain ⟨a,ha⟩ := (FiberCoreMap.fiber_bijective (Z n) (core X f I δ Z pot hBase hPot hCoord)
      (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
      (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
      (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q) x).2
      ⟨e,hx.symm⟩
    exact ⟨a.1,congrArg Subtype.val ha⟩

variable [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in
lemma coverIncl_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (coverIncl X f I δ Z pot hBase hPot hCoord n) := by
  refine ⟨FiberCoreMap.isEmbedding (Z n) (core X f I δ Z pot hBase hPot hCoord)
    (SequentialColimit.incl X f n) (fun a => ⟨n,a⟩)
    (fun a x hx => (baseSet_incl X f I δ Z pot hBase hPot hCoord n a x).mpr hx)
    (fun a b x _ q => coordChange_incl X f I δ Z pot hBase hPot hCoord n a b x q)
    (SequentialColimit.incl_isClosedEmbedding X f hf n).isEmbedding,?_⟩
  rw [coverIncl_range]
  exact (SequentialColimit.incl_isClosedEmbedding X f hf n).isClosed_range.preimage
    (core X f I δ Z pot hBase hPot hCoord).continuous_proj

end SequentialCoreTower

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimitRangeInclMono
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SequentialColimit
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

lemma range_incl_mono {i j : ℕ} (h : i ≤ j) : range (incl X f i) ⊆ range (incl X f j) := by
  rintro _ ⟨x,rfl⟩
  exact ⟨f i j h x,incl_map X f i j h x⟩

lemma finite_subset_stage {K : Set (Space X f)} (hK : K.Finite) :
    ∃ n, K ⊆ range (incl X f n) := by
  induction K,hK using Set.Finite.induction_on with
  | empty => exact ⟨0,empty_subset _⟩
  | @insert x S hx hS ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,y,rfl⟩ := DirectLimit.exists_eq_mk f x
    refine ⟨max m n,?_⟩
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact range_incl_mono X f (le_max_left _ _) (mem_range_self y)
    · exact range_incl_mono X f (le_max_right _ _) (hn hz)

lemma isClosed_iff_stages (S : Set (Space X f)) :
    IsClosed S ↔ ∀ n, IsClosed (incl X f n ⁻¹' S) := by
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage,isClosed_sigma_iff]
  rfl

variable [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

lemma compact_subset_stage (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)]
    (hf : ∀ i j h, IsClosedEmbedding (f i j h))
    {K : Set (Space X f)} (hK : IsCompact K) :
    ∃ n, K ⊆ range (incl X f n) := by
  classical
  let := hausdorff X f hf
  by_contra hbound
  have hex (n : ℕ) : ∃ z, z ∈ K ∧ z ∉ range (incl X f n) := by
    by_contra h
    apply hbound
    refine ⟨n,?_⟩
    intro z hz
    by_contra hn
    exact h ⟨z,hz,hn⟩
  choose z hzK hzN using hex
  have hc (T : Set (Space X f)) (hT : T ⊆ range z) : IsClosed T := by
    apply (isClosed_iff_stages X f T).mpr
    intro n
    apply Set.Finite.isClosed
    apply (Set.Finite.preimage (incl_injective X f (fun i j h => (hf i j h).injective) n).injOn
      ((finite_Iio n).image z)).subset
    intro x hx
    obtain ⟨m,hm⟩ := hT hx
    refine ⟨m,?_,hm⟩
    change m < n
    by_contra hmn
    exact hzN m (range_incl_mono X f (le_of_not_gt hmn) (hm ▸ mem_range_self x))
  have hd : IsDiscrete (range z) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T,hc T hT,inter_eq_left.mpr hT⟩
  have hkr : IsCompact (range z) := hK.of_isClosed_subset (hc _ Subset.rfl) (by
    rintro _ ⟨n,rfl⟩
    exact hzK n)
  obtain ⟨n,hn⟩ := finite_subset_stage X f (hkr.finite hd)
  exact hzN n (hn (mem_range_self n))

end SequentialColimit

namespace SequentialCoreTower
open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)
  [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))

include hf in

lemma compact_map_factors_above {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (g : C(A,(core X f I δ Z pot hBase hPot hCoord).TotalSpace)) (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ ∃ h : C(A,(Z n).TotalSpace),
      ∀ a, coverIncl X f I δ Z pot hBase hPot hCoord n (h a) = g a := by
  let p := core X f I δ Z pot hBase hPot hCoord
  obtain ⟨m,hm⟩ := SequentialColimit.compact_subset_stage X f hf
    (isCompact_range (p.continuous_proj.comp g.continuous))
  let n := max m N
  have hn (a : A) : g a ∈ range (coverIncl X f I δ Z pot hBase hPot hCoord n) := by
    rw [coverIncl_range]
    exact SequentialColimit.range_incl_mono X f (le_max_left _ _) (hm (mem_range_self a))
  let e := (coverIncl_isClosedEmbedding X f I δ Z pot hBase hPot hCoord hf n).isEmbedding.toHomeomorph
  let h : C(A,(Z n).TotalSpace) := ⟨fun a => e.symm ⟨g a,hn a⟩,
    e.symm.continuous.comp (g.continuous.subtype_mk hn)⟩
  exact ⟨n,le_max_right _ _,h,fun a => congrArg Subtype.val (e.apply_symm_apply ⟨g a,hn a⟩)⟩

end SequentialCoreTower

namespace SequentialCW
open Set Topology Metric
universe u
variable (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
  [∀ i, CWComplex (univ : Set (X i))]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
variable (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
  [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
  (hδ : ∀ i j h n (c : Cell X i n) v, v ∈ closedBall (0 : Fin n → ℝ) 1 →
    f i j h (RelCWComplex.map n c v) = RelCWComplex.map n (δ i j h n c) v)

lemma cellMk_surjective (n N : ℕ)
    (hst : ∀ i (h : N ≤ i), Function.Surjective (δ N i h n)) :
    Function.Surjective (cellMk X δ N n) := by
  intro c
  obtain ⟨i,c,rfl⟩ := DirectLimit.exists_eq_mk (fun i j h => δ i j h n) c
  by_cases hi : i ≤ N
  · exact ⟨δ i N hi n c,cellMk_map X δ i N hi n c⟩
  · obtain ⟨c,rfl⟩ := hst i (by omega) c
    exact ⟨c,(cellMk_map X δ N i (by omega) n c).symm⟩

lemma finiteType [∀ i, RelCWComplex.FiniteType (univ : Set (X i))]
    (hst : ∀ n, ∃ N, ∀ i (h : N ≤ i), Function.Surjective (δ N i h n)) :
    letI := cwComplex X f hf δ hδ
    RelCWComplex.FiniteType (univ : Set (Space X f)) := by
  let := cwComplex X f hf δ hδ
  constructor
  intro n
  obtain ⟨N,hN⟩ := hst n
  let : Finite (Cell X N n) := RelCWComplex.FiniteType.finite_cell n
  exact Finite.of_surjective (cellMk X δ N n) (cellMk_surjective X δ n N hN)

end SequentialCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWWhitehead
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SequentialCoreTower
open Set Topology Metric
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)
  [∀ n, T2Space (X n)] [∀ n, NormalSpace (X n)] [∀ n, CompactSpace (X n)]
  [∀ n, Nonempty (X n)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
  (hπ : ∀ n p, p ≤ n → ∀ z : (Z n).TotalSpace,
    Subsingleton (HomotopyGroup (Fin p) (Z n).TotalSpace z))

include hf hπ in

lemma sphereFill : CWCylinder.SphereFill (core X f I δ Z pot hBase hPot hCoord).TotalSpace := by
  intro n g
  obtain ⟨k,hk,h,hh⟩ := compact_map_factors_above X f I δ Z pot hBase hPot hCoord hf g n
  have hn : h.Nullhomotopic := by
    cases n with
    | zero =>
      let : IsEmpty (CWExtension.Boundary 0) := ⟨fun v => by
        have hv : ‖v.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using v.2
        have he : v.1 = 0 := Subsingleton.elim _ _
        rw [he,norm_zero] at hv
        exact zero_ne_one hv⟩
      obtain ⟨x⟩ := (inferInstance : Nonempty (X k))
      let z : (Z k).TotalSpace := ⟨x,(1:Q)⟩
      have he : h = .const (CWExtension.Boundary 0) z := by
        apply ContinuousMap.ext
        intro v
        exact isEmptyElim v
      rw [he]
      exact ContinuousMap.nullhomotopic_of_constant z
    | succ p =>
      let := hπ k p (by omega) (h (SphereQuotient.pole p))
      exact WeakSphere.sphere_nullhomotopic p h
  obtain ⟨H,hH⟩ := SphereExtension.exists_extension h hn
  exact ⟨(coverIncl X f I δ Z pot hBase hPot hCoord k).comp H,fun v => by
    change coverIncl X f I δ Z pot hBase hPot hCoord k (H _) = g v
    exact (congrArg (coverIncl X f I δ Z pot hBase hPot hCoord k) (hH v)).trans (hh v)⟩

include hf hπ in

lemma contractible [DiscreteTopology Q]
    [CWComplex (univ : Set (SequentialColimit.Space X f))] :
    ContractibleSpace (core X f I δ Z pot hBase hPot hCoord).TotalSpace := by
  let W := core X f I δ Z pot hBase hPot hCoord
  let := SequentialColimit.hausdorff X f hf
  let := CoveringCellGeometry.hausdorff (core_covering X f I δ Z pot hBase hPot hCoord)
  let := CoveringCW.cwComplex_general (core_covering X f I δ Z pot hBase hPot hCoord)
  obtain ⟨x⟩ := (inferInstance : Nonempty (X 0))
  let z : W.TotalSpace := ⟨SequentialColimit.incl X f 0 x,(1:Q)⟩
  let e := Homeomorph.Set.univ W.TotalSpace
  let H := CWWhitehead.homotopy (sphereFill X f I δ Z pot hBase hPot hCoord hf hπ)
    (⟨e,e.continuous⟩ : C((univ : Set W.TotalSpace),W.TotalSpace)) (.const _ z)
  apply (contractible_iff_id_nullhomotopic W.TotalSpace).mpr
  refine ⟨z,⟨?_⟩⟩
  exact { toFun := fun v => H (v.1,e.symm v.2)
          continuous_toFun := H.continuous.comp
            (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
          map_zero_left := fun y => (H.map_zero_left (e.symm y)).trans (e.apply_symm_apply y)
          map_one_left := fun y => H.map_one_left (e.symm y) }

end SequentialCoreTower

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PresentationGeometry.PresentationComplex.transported_simplyConnected _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry
open Set Topology
universe u
variable (G : Type u) [Group G]

theorem exists_word_presentation [Group.IsFinitelyPresented G] :
    ∃ (k r : ℕ) (w : Fin r → List (Fin k × Bool)),
      Nonempty (G ≃* PresentedGroup (PresentationComplex.relatorSet w)) := by
  classical
  obtain ⟨k,φ,hφ,S,hfin,hS⟩ := Group.IsFinitelyPresented.out (G := G)
  let := hfin.fintype
  let r := Fintype.card S
  let e : Fin r ≃ S := (Fintype.equivFin S).symm
  let w : Fin r → List (Fin k × Bool) := fun i => (e i).1.toWord
  have hw : PresentationComplex.relatorSet w = S := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      simpa only [w,FreeGroup.mk_toWord] using (e i).2
    · intro hx
      obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
      refine ⟨i,?_⟩
      change FreeGroup.mk (e i).1.toWord = x
      rw [FreeGroup.mk_toWord]
      exact congrArg Subtype.val hi
  refine ⟨k,r,w,?_⟩
  have hc : Subgroup.normalClosure (PresentationComplex.relatorSet w) = φ.ker := by
    rw [hw,hS]
  let q : PresentedGroup (PresentationComplex.relatorSet w) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact ⟨q.symm⟩

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.FiniteStage
section
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
lemma initialStage_exists [Group.IsFinitelyPresented Q] : Nonempty (Stage Q 0) := by
  obtain ⟨k,r,w,⟨e⟩⟩ := exists_word_presentation Q
  exact ⟨PresentationComplex.initialStage w e⟩
end

section
open Set Topology Metric Cells CWExtension CellCoverExtension
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {n : ℕ} (S : Stage Q n) (A : Attachment S)

lemma cellStep_surjective (d : ℕ) (hd : d ≠ n+3) : Function.Surjective (cellStep S A d) := by
  intro c
  change NewCell (X:=S.X) (k:=A.k) (d:=n+3) d at c
  rcases c with c | ⟨i,⟨he⟩⟩
  · exact ⟨c,rfl⟩
  · exact (hd he).elim

end

open Set Topology Metric
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))

lemma stageCell_stable (d i : ℕ) (h : d ≤ i) : Function.Surjective (stageCell S₀ hzero d i h d) := by
  induction i,h using Nat.le_induction with
  | base =>
    intro c; refine ⟨c,?_⟩
    simp only [stageCell,Function.Embedding.coeFn_mk,Nat.leRecOn_self]
  | succ i h ih =>
    intro c
    obtain ⟨c,rfl⟩ := cellStep_surjective (stages S₀ hzero i) (attachments S₀ hzero i) d (by omega) c
    obtain ⟨c,rfl⟩ := ih c
    exact ⟨c,stageCell_succ S₀ hzero d i h _ d c⟩
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationGeometry.FiniteStage
open Set Topology _root_.CategoryTheory CategoryTheory.Limits
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) m))
lemma finalFiniteType :
    letI := finalCW S₀ hzero
    RelCWComplex.FiniteType (univ : Set (finalSpace S₀ hzero)) :=
  SequentialCW.finiteType (stageX S₀ hzero) (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
    (stageCell S₀ hzero) (fun i j h d c v _ => stageMap_chart S₀ hzero i j h d c v)
    (fun d => ⟨d,stageCell_stable S₀ hzero d⟩)
lemma finalCore_contractible : ContractibleSpace (finalCore S₀ hzero).TotalSpace := by
  let := finalCW S₀ hzero
  exact SequentialCoreTower.contractible (stageX S₀ hzero) (stageMap S₀ hzero)
    (stageI S₀ hzero) (stageIndex S₀ hzero) (fun n => (stages S₀ hzero n).core)
    (fun n => (stages S₀ hzero n).pot) (stage_base S₀ hzero) (stage_pot S₀ hzero)
    (fun n => (stages S₀ hzero n).coord) (stageMap_closed S₀ hzero)
    (fun n p hp z => (stages S₀ hzero n).connectivity p (by omega) z)
lemma finalCore_regular (i j x a q) :
    (finalCore S₀ hzero).coordChange i j x (a*q) =
      (finalCore S₀ hzero).coordChange i j x a * q := by
  change _ * (a*q) = (_ * a) * q
  exact (mul_assoc _ a q).symm
include S₀ hzero in

lemma geometric_of_initial : SimpleFInftyOvergroups.HasTypeFInfty Q := by
  let X := finalSpace S₀ hzero
  let W := finalCore S₀ hzero
  let := finalCW S₀ hzero
  let : T2Space X := SequentialColimit.hausdorff (stageX S₀ hzero)
    (stageMap S₀ hzero) (stageMap_closed S₀ hzero)
  let : ContractibleSpace W.TotalSpace := finalCore_contractible S₀ hzero
  have hsur : Function.Surjective W.proj := fun x => ⟨⟨x,(1:Q)⟩,rfl⟩
  let : PathConnectedSpace X := hsur.pathConnectedSpace W.continuous_proj
  let x : X := SequentialColimit.incl (stageX S₀ hzero) (stageMap S₀ hzero) 0 S₀.point
  refine ⟨X,inferInstance,finalCW S₀ hzero,inferInstance,inferInstance,
    finalFiniteType S₀ hzero,x,?_,W.TotalSpace,inferInstance,W.proj,
    DiscreteCoverCharts.covering W,hsur,inferInstance⟩
  exact ⟨CoreDeck.leftFundamentalEquiv W (finalCore_regular S₀ hzero) x⟩
end PresentationGeometry.FiniteStage

namespace SimpleFInftyOvergroups
open CategoryTheory.Limits

theorem geometric_product_criterion (Q : Type) [Group Q] [Group.IsFinitelyPresented Q]
    (hzero : ∀ I : Type, ∀ n ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) n)) :
    HasTypeFInfty Q := by
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  obtain ⟨S₀⟩ := PresentationGeometry.FiniteStage.initialStage_exists Q
  exact PresentationGeometry.FiniteStage.geometric_of_initial S₀ hzero
end SimpleFInftyOvergroups

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule

open scoped MonoidalCategory
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

namespace ActionPresentation

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
lemma fg_of_fp [Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨n,f,hf,_⟩ := (inferInstance : Group.IsFinitelyPresented G).out
  exact Group.fg_of_surjective hf

end ActionPresentation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.LocalEmbedding.instCoeFunForallBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin

lemma continuous_get (n : ℕ) : Continuous (fun x : Cantor => x.get n) := continuous_apply n

end TwistedBrin

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma isOpen_brick (p : Prefix S) : IsOpen p.brick := by
  classical
  let : Finite {s : S // p s ≠ []} := p.finite_support.to_subtype
  let I := (s : {s : S // p s ≠ []}) × Fin (p s.1).length
  have he : p.brick = ⋂ j : I, {x | (x j.1.1).get j.2 = (p j.1.1)[j.2]} := by
    ext x
    simp only [mem_brick_iff_get,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h j; exact h j.1.1 j.2 j.2.isLt
    · intro h s n hn
      have hs : p s ≠ [] := by intro he; simp [he] at hn
      exact h ⟨⟨s,hs⟩,⟨n,hn⟩⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_discrete {(p j.1.1)[j.2]}).preimage
    ((continuous_get (j.2.val)).comp (continuous_apply j.1.1))

end TwistedBrin.Prefix

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma finite_grid_refinement (I : Finset (Box S)) (p : Box S → Prefix S)
    (hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick) :
    ∃ b : S →₀ ℕ, ∀ z : Prefix.Grid b, ∃ i ∈ I,
      Prefix.Extends (p i) (Prefix.gridPrefix b z) := by
  classical
  let b : S →₀ ℕ := ∑ i ∈ I, (p i).lengths
  refine ⟨b,?_⟩
  intro z
  let x : Box S := (Prefix.gridPrefix b z).chart (fun _ _ => false)
  obtain ⟨i,hi,hix⟩ := hc x
  refine ⟨i,hi,Prefix.extends_of_mem_of_length_le hix (Prefix.chart_mem_brick _ _) ?_⟩
  intro s
  rw [Prefix.gridPrefix_length]
  change (p i).lengths s ≤ b s
  have hl : (p i).lengths ≤ ∑ j ∈ I, (p j).lengths :=
    Finset.single_le_sum (f := fun j => (p j).lengths) (fun _ _ s => Nat.zero_le _) hi
  exact hl s

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderBasedComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderBasedComplex

variable {B : Type*} (C : Data B)

lemma d_vertex {b : B} (hb : C.degree b = 0) : C.d (Finsupp.single b 1) = 0 := by
  classical
  apply Finsupp.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have H := C.lowers b t ht
  omega

lemma linear_eq_on_support {M : Type*} [AddCommGroup M]
    (f g : (B →₀ ℤ) →ₗ[ℤ] M) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) = g (Finsupp.single b 1)) : f c = g c := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c]
  conv_rhs => rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul, LinearMap.map_smul, h b hb]

end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains

variable (G : Type*)

lemma degree_cone (a : G) (s : Simplex G) :
    degree G (simplexCone G a s) = degree G s + 1 := rfl

lemma boundary_vertices (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    vertices G t ⊆ vertices G s := (boundary_faces G s t ht).2

lemma cone_mem_degreeModule {n : ℕ} (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : cone G a c ∈ degreeModule G (n+1) := by
  refine supported_cone G (Q := fun s => degree G s = n+1) a ?_ hc
  intro s hs
  rw [degree_cone, hs]

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
lemma cone_carrier (x : P) {c : Chain P} (hc : c ∈ carrier P x) :
    cone P x c ∈ carrier P x := by
  refine supported_cone P (P := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x)
    (Q := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x) x ?_ hc
  intro s hs
  constructor
  · change (x :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun v hv => hs.2 v ((mem_list P s v).mp hv),hs.1⟩
  · rw [vertices_cone]
    intro v hv
    rcases hv with rfl | hv
    · exact le_rfl
    · exact hs.2 v hv

variable {Q : Type*} [Preorder Q]

lemma mapChain_comp (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]
    {R : Type*} (f : P → Q) (g : Q → R) (c : Chain P) :
    mapChain Q g (mapChain P f c) = mapChain P (g ∘ f) c := by
  have h : (mapChain Q g).comp (mapChain P f) = mapChain P (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply,mapChain_single,List.map_map,Function.comp_apply]
  exact LinearMap.congr_fun h c
lemma mapChain_id (P : Type*) [Preorder P] (c : Chain P) : mapChain P id c = c := by
  have h : mapChain P id = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [mapChain_single,id_eq,List.map_id,LinearMap.id_coe]
  exact LinearMap.congr_fun h c

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfTop
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace OrderBasedComplex
section
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (point : B → M) (fill : B → ℕ → M → M)

lemma chosen_vertex {b : B} (hb : C.degree b = 0) :
    chosenExtend C point fill (Finsupp.single b 1) = point b := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_left hb]
lemma chosen_positive {b : B} (hb : C.degree b ≠ 0) :
    chosenExtend C point fill (Finsupp.single b 1) =
      fill b (C.degree b-1) (chosenExtend C point fill (C.d (Finsupp.single b 1))) := by
  simp only [chosenExtend,Finsupp.linearCombination_single,one_smul]
  rw [chosenBasis,ite_eq_right hb]
  congr 1
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenBasis C point fill t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hpoint : ∀ b, P b → point b ∈ K b ∧ point b ∈ D 0 ∧ d (point b) = 0 ∧ aug (point b) = 1)
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hpoint hfill in
lemma chosen_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N+1) :
    chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
    chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
    d (chosenExtend C point fill (Finsupp.single b 1)) =
      chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
    aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N+1 →
      chosenExtend C point fill (Finsupp.single b 1) ∈ K b ∧
      chosenExtend C point fill (Finsupp.single b 1) ∈ D (C.degree b) ∧
      d (chosenExtend C point fill (Finsupp.single b 1)) =
        chosenExtend C point fill (C.d (Finsupp.single b 1)) ∧
      aug (chosenExtend C point fill (Finsupp.single b 1)) = C.aug (Finsupp.single b 1) by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    by_cases hz : C.degree b = 0
    · rw [chosen_vertex C point fill hz,hz,d_vertex C hz,map_zero,C.aug_single,ite_eq_left hz]
      exact hpoint b hb
    · have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
        ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
          (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
      let z := chosenExtend C point fill (C.d (Finsupp.single b 1))
      have hzK : z ∈ K b := by
        apply map_mem_of_support
        intro t ht
        exact hface b t hb ht (hs t ht).1
      have hzD : z ∈ D (C.degree b-1) := by
        apply map_mem_of_support
        intro t ht
        have hh := C.lowers b t ht
        have he : C.degree b - 1 = C.degree t := by omega
        rw [he]
        exact (hs t ht).2.1
      have hzd : d z = 0 := by
        have he := linear_eq_on_support (d.comp (chosenExtend C point fill))
          ((chosenExtend C point fill).comp C.d) (C.d (Finsupp.single b 1))
          (fun t ht => (hs t ht).2.2.1)
        change d z = _ at he
        simpa only [LinearMap.comp_apply,C.d_squared,map_zero] using he
      have hza : aug z = 0 := by
        have he := linear_eq_on_support (aug.comp (chosenExtend C point fill)) C.aug
          (C.d (Finsupp.single b 1)) (fun t ht => (hs t ht).2.2.2)
        change aug z = _ at he
        simpa only [C.aug_d] using he
      obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b-1) (by omega) z hzK hzD hzd hza
      rw [chosen_positive C point fill hz]
      refine ⟨hK,?_,hd,?_⟩
      · have he : C.degree b - 1 + 1 = C.degree b := by omega
        simpa only [he] using hD
      · rw [C.aug_single,ite_eq_right hz]
        exact ha

end

variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (fill : B → ℕ → M → M) (F G : (B →₀ ℤ) →ₗ[ℤ] M)

lemma chosenHomotopy_equation (b : B) :
    chosenHomotopy C fill F G (Finsupp.single b 1) =
      fill b (C.degree b) (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1))) := by
  simp only [chosenHomotopy,Finsupp.linearCombination_single,one_smul]
  rw [chosenHomotopyBasis]
  congr 2
  simp only [Finsupp.linearCombination_apply,Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => C.d (Finsupp.single b 1) t • chosenHomotopyBasis C fill F G t)

variable (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ)
  (D : ℕ → Submodule ℤ M) (P : B → Prop) (K : B → Submodule ℤ M) (N : ℕ)
  (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
  (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
  (hF : ∀ b, P b → C.degree b ≤ N → F (Finsupp.single b 1) ∈ K b ∧
    F (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (F (Finsupp.single b 1)) = F (C.d (Finsupp.single b 1)) ∧
    aug (F (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hG : ∀ b, P b → C.degree b ≤ N → G (Finsupp.single b 1) ∈ K b ∧
    G (Finsupp.single b 1) ∈ D (C.degree b) ∧ d (G (Finsupp.single b 1)) = G (C.d (Finsupp.single b 1)) ∧
    aug (G (Finsupp.single b 1)) = C.aug (Finsupp.single b 1))
  (hfill : ∀ b, P b → ∀ n ≤ N, ∀ z : M, z ∈ K b → z ∈ D n → d z = 0 → aug z = 0 →
    fill b n z ∈ K b ∧ fill b n z ∈ D (n+1) ∧ d (fill b n z) = z ∧ aug (fill b n z) = 0)

include hP hface hF hG hfill in
lemma chosenHomotopy_spec (b : B) (hb : P b) (hbn : C.degree b ≤ N) :
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
    chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
    d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
      chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
      F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
    aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 := by
  suffices ∀ m b, C.degree b = m → P b → m ≤ N →
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ K b ∧
      chosenHomotopy C fill F G (Finsupp.single b 1) ∈ D (C.degree b+1) ∧
      d (chosenHomotopy C fill F G (Finsupp.single b 1)) +
        chosenHomotopy C fill F G (C.d (Finsupp.single b 1)) =
        F (Finsupp.single b 1) - G (Finsupp.single b 1) ∧
      aug (chosenHomotopy C fill F G (Finsupp.single b 1)) = 0 by
    exact this _ b rfl hb hbn
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro b hm hb hbn
    have hbn' : C.degree b ≤ N := by omega
    have hfs := hF b hb hbn'
    have hgs := hG b hb hbn'
    have hs (t : B) (ht : t ∈ (C.d (Finsupp.single b 1)).support) :=
      ih (C.degree t) (by have hh := C.lowers b t ht; omega) t rfl
        (hP b t hb ht) (by have hh := C.lowers b t ht; omega)
    let H := chosenHomotopy C fill F G
    let z := F (Finsupp.single b 1) - G (Finsupp.single b 1) - H (C.d (Finsupp.single b 1))
    have hzK : z ∈ K b := by
      apply (K b).sub_mem ((K b).sub_mem hfs.1 hgs.1)
      apply map_mem_of_support
      intro t ht
      exact hface b t hb ht (hs t ht).1
    have hzD : z ∈ D (C.degree b) := by
      apply (D _).sub_mem ((D _).sub_mem hfs.2.1 hgs.2.1)
      apply map_mem_of_support
      intro t ht
      rw [← C.lowers b t ht]
      exact (hs t ht).2.1
    have hzd : d z = 0 := by
      have he := linear_eq_on_support (d.comp H) (F-G-H.comp C.d)
        (C.d (Finsupp.single b 1)) (fun t ht => by
          have hh := (hs t ht).2.2.1
          change d (H (Finsupp.single t 1)) = _
          simpa only [LinearMap.sub_apply,LinearMap.comp_apply] using eq_sub_of_add_eq hh)
      simp only [LinearMap.sub_apply,LinearMap.comp_apply,C.d_squared,map_zero,sub_zero] at he
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.1,hgs.2.2.1,he,sub_self]
    have hza : aug z = 0 := by
      have he := linear_eq_on_support (aug.comp H) 0 (C.d (Finsupp.single b 1))
        (fun t ht => (hs t ht).2.2.2)
      dsimp only [z]
      rw [map_sub,map_sub,hfs.2.2.2,hgs.2.2.2,sub_self]
      change 0 - (aug.comp H) (C.d (Finsupp.single b 1)) = 0
      rw [he,LinearMap.zero_apply,sub_zero]
    obtain ⟨hK,hD,hd,ha⟩ := hfill b hb (C.degree b) hbn' z hzK hzD hzd hza
    rw [chosenHomotopy_equation]
    refine ⟨hK,hD,?_,ha⟩
    rw [hd]
    dsimp only [z,H]
    abel
end OrderBasedComplex

namespace OrderListChains
variable (P : Type*)
lemma augmentation_of_positive {n : ℕ} (hn : 0 < n) {c : Chain P}
    (hc : Homogeneous P n c) : augmentation P c = 0 := by
  have he := OrderBasedComplex.linear_eq_on_support (augmentation P) 0 c (fun s hs => by
    rw [augmentation_single,ite_eq_right,LinearMap.zero_apply]
    intro h
    have hh := hc s hs
    simp only [degree,h,List.length_nil] at hh
    omega)
  exact he
end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsOnSet
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
lemma onSet_mono {U V : Set P} (h : U ⊆ V) : onSet P U ≤ onSet P V :=
  fun _ hc _ hs => ⟨(hc hs).1, fun _ hx => h ((hc hs).2 hx)⟩
lemma onSet_le_module (U : Set P) : onSet P U ≤ module P :=
  fun _ hc _ hs => (hc hs).1
lemma map_onSet {Q : Type*} [Preorder Q] (f : P → Q) {U : Set P} {V : Set Q}
    (hf : ∀ x ∈ U, f x ∈ V) (hm : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → f x ≤ f y)
    {c : Chain P} (hc : c ∈ onSet P U) : mapChain P f c ∈ onSet Q V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  constructor
  · change ((list P s).map f).Pairwise _
    rw [List.pairwise_map]
    apply (hc hs).1.imp_of_mem
    intro x y hx hy hxy
    exact hm y ((hc hs).2 ((mem_list P s y).mp hy))
      x ((hc hs).2 ((mem_list P s x).mp hx)) hxy
  · intro y hy
    rcases hy with rfl | hy
    · exact hf s.1 ((hc hs).2 (head_mem_vertices P s))
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      exact hf x ((hc hs).2 (Or.inr hx))

lemma project_val (P : Type*) [Preorder P] {U : Set P} (u : U) {x : P} (hx : x ∈ U) :
    (project P U u x).val = x := by
  classical
  simp [project,hx]
lemma project_include {U : Set P} (u v : U) : project P U u v = v := by
  apply Subtype.ext
  exact project_val P u v.property

lemma cone_onSet_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    {c : Chain P} (hc : c ∈ onSet P U) : cone P u c ∈ onSet P U := by
  change Supported P (fun s => Descending P s ∧ vertices P s ⊆ U) (cone P u c)
  refine supported_cone P (P := fun s => Descending P s ∧ vertices P s ⊆ U) u ?_ hc
  intro s hs
  constructor
  · change (u :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun x hx => ht x (hs.2 ((mem_list P s x).mp hx)),hs.1⟩
  · rw [vertices_cone]
    exact Set.insert_subset hu hs.2
lemma exactSet_of_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    (n : ℕ) : ExactSet P U n := by
  intro c hc hn hd ha
  refine ⟨cone P u c,cone_onSet_top P u hu ht hc,cone_mem_degreeModule P _ hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]

lemma cycleFill_spec {U : Set P} {n : ℕ} (hU : ExactSet P U n) {c : Chain P}
    (hc : c ∈ onSet P U) (hn : Homogeneous P n c) (hd : boundary P c = 0)
    (ha : augmentation P c = 0) :
    cycleFill P U n c ∈ onSet P U ∧ Homogeneous P (n+1) (cycleFill P U n c) ∧
    boundary P (cycleFill P U n c) = c ∧ augmentation P (cycleFill P U n c) = 0 := by
  have he := hU c hc hn hd ha
  classical
  simp only [cycleFill,dite_eq_left he]
  exact ⟨(Classical.choose_spec he).1,(Classical.choose_spec he).2.1,
    (Classical.choose_spec he).2.2,augmentation_of_positive P (n := n+1) (by omega) (Classical.choose_spec he).2.1⟩

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsVertexSupport
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
variable (P : Type*)
lemma mem_vertexSupport {c : Chain P} {x : P} : x ∈ vertexSupport P c ↔
    ∃ s ∈ c.support, x ∈ vertices P s := by
  classical
  simp only [vertexSupport,Finset.mem_biUnion,List.mem_toFinset,mem_list]
end OrderListChains

namespace OrderChains

section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem carrier_fill (U V : Set P) (K L : Simplex P → Set P) (N : ℕ)
    (hKne : ∀ s, Descending P s → vertices P s ⊆ U → (K s).Nonempty)
    (hKV : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ V)
    (hLU : ∀ s, Descending P s → vertices P s ⊆ U → L s ⊆ U)
    (hKL : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ L s)
    (hself : ∀ s, Descending P s → vertices P s ⊆ U → vertices P s ⊆ L s)
    (hfaceK : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → K t ⊆ K s)
    (hfaceL : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → L t ⊆ L s)
    (hKexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (K s) k)
    (hLexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (L s) k)
    (hVU : V ⊆ U)
    (hLV : ∀ s, Descending P s → vertices P s ⊆ V → L s ⊆ V)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hcV : c ∈ onSet P V) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0)
    (hb : b ∈ onSet P U) (hbn : Homogeneous P (n+1) b) (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P V ∧ Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  have _ := hLU
  have _ := ha
  have hc : c ∈ onSet P U := onSet_mono P hVU hcV
  let valid : Simplex P → Prop := fun s => Descending P s ∧ vertices P s ⊆ U
  let p : Simplex P → P := fun s => if h : valid s then (hKne s h.1 h.2).choose else s.1
  let point : Simplex P → Chain P := fun s => vertex P (p s)
  let fill := fun s k z => cycleFill P (K s) k z
  let F := OrderBasedComplex.chosenExtend (based P) point fill
  have hvalid : ∀ s t, valid s → t ∈ (boundary P (Finsupp.single s 1)).support → valid t := by
    intro s t hs ht
    exact ⟨hs.1.boundary P ht,(boundary_vertices P s t ht).trans hs.2⟩
  have hpoint (s : Simplex P) (hs : valid s) : point s ∈ onSet P (K s) ∧
      point s ∈ degreeModule P 0 ∧ boundary P (point s) = 0 ∧ augmentation P (point s) = 1 := by
    have hp : p s ∈ K s := by
      dsimp only [p]
      rw [dite_eq_left hs]
      exact (hKne s hs.1 hs.2).choose_spec
    refine ⟨?_,?_,boundary_vertex P _,augmentation_vertex P _⟩
    · apply supported_single
      exact ⟨List.pairwise_singleton _ _,by rw [vertices_vertex]; exact Set.singleton_subset_iff.mpr hp⟩
    · change Homogeneous P 0 (Finsupp.single (simplexVertex P (p s)) 1)
      exact supported_single P (P := fun t => degree P t = 0) rfl 1
  have hfill (s : Simplex P) (hs : valid s) (k : ℕ) (hk : k ≤ N) (z : Chain P)
      (hz : z ∈ onSet P (K s)) (hzdeg : z ∈ degreeModule P k)
      (hzd : boundary P z = 0) (hza : augmentation P z = 0) :=
    cycleFill_spec P (hKexact s hs.1 hs.2 k hk) hz hzdeg hzd hza
  have hF (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N+1) :
      F (Finsupp.single s 1) ∈ onSet P (K s) ∧
      F (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P (F (Finsupp.single s 1)) = F (boundary P (Finsupp.single s 1)) ∧
      augmentation P (F (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact OrderBasedComplex.chosen_spec (based P) point fill (boundary P) (augmentation P)
      (degreeModule P) valid (fun s => onSet P (K s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceK s t hs.1 hs.2 ht)) hpoint hfill s hs hdeg
  let fillL := fun s k z => cycleFill P (L s) k z
  let H := OrderBasedComplex.chosenHomotopy (based P) fillL LinearMap.id F
  have hI (s : Simplex P) (hs : valid s) (_ : degree P s ≤ N) :
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ onSet P (L s) ∧
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (boundary P (Finsupp.single s 1)) ∧
      augmentation P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact ⟨supported_single P ⟨hs.1,hself s hs.1 hs.2⟩ 1,
      supported_single P (P := fun t => degree P t = degree P s) rfl 1,rfl,rfl⟩
  have hFL (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :=
    hF s hs (by omega)
  have hH (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :
      H (Finsupp.single s 1) ∈ onSet P (L s) ∧
      H (Finsupp.single s 1) ∈ degreeModule P (degree P s+1) ∧
      boundary P (H (Finsupp.single s 1)) + H (boundary P (Finsupp.single s 1)) =
        Finsupp.single s 1 - F (Finsupp.single s 1) ∧
      augmentation P (H (Finsupp.single s 1)) = 0 := by
    apply OrderBasedComplex.chosenHomotopy_spec (based P) fillL LinearMap.id F (boundary P)
      (augmentation P) (degreeModule P) valid (fun s => onSet P (L s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceL s t hs.1 hs.2 ht)) hI ?_ ?_ s hs hdeg
    · intro t ht htd
      exact ⟨onSet_mono P (hKL t ht.1 ht.2) (hFL t ht htd).1,(hFL t ht htd).2⟩
    · intro t ht k hk z hz hzdeg hzd hza
      exact cycleFill_spec P (hLexact t ht.1 ht.2 k hk) hz hzdeg hzd hza
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  have hbdg (s : Simplex P) (hs : s ∈ b.support) : degree P s ≤ N+1 := by rw [hbn s hs]; omega
  refine ⟨F b + H c, (onSet P V).add_mem ?_ ?_, supported_add P ?_ ?_, ?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hKV t (hb ht).1 (hb ht).2) (hF t (hb ht) (hbdg t ht)).1
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hLV t (hcV ht).1 (hcV ht).2) (hH t (hc ht) (hsd t ht)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule P (n+1))
    intro t ht
    rw [← hbn t ht]
    exact (hF t (hb ht) (hbdg t ht)).2.1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro t ht
    rw [← hn t ht]
    exact (hH t (hc ht) (hsd t ht)).2.1
  · have hFb := OrderBasedComplex.linear_eq_on_support ((boundary P).comp F) (F.comp (boundary P)) b
      (fun t ht => (hF t (hb ht) (hbdg t ht)).2.2.1)
    have hHc := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-F) c (fun t ht => (hH t (hc ht) (hsd t ht)).2.2.1)
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      hd,map_zero,add_zero] at hHc
    simp only [LinearMap.comp_apply,hbd] at hFb
    rw [map_add,hFb,hHc]
    abel
end

open OrderListChains
variable (P : Type*) [PartialOrder P]

lemma lowerCarrier_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerCarrier P r h t ⊆ lowerCarrier P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  have hdt := hs.boundary P ht
  unfold lowerCarrier
  split_ifs with hT hS hS
  · have he : t.1 = s.1 := by
      apply le_antisymm hts
      by_contra hn
      have hh := hr (lt_of_le_not_ge hts hn)
      omega
    simpa only [he] using (Set.Subset.rfl : Set.Iio s.1 ⊆ Set.Iio s.1)
  · omega
  · intro x hx
    have hxt := hdt.le_head P hx
    apply lt_of_le_of_ne (hxt.trans hts)
    intro he
    have hh := hr.monotone hxt
    rw [he] at hh
    omega
  · exact hv

lemma lowerStar_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerStar P r h t ⊆ lowerStar P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  unfold lowerStar
  split_ifs with hT hS hS
  · exact fun _ hx => hx.trans hts
  · omega
  · exact fun _ hx => hs.le_head P (hv hx)
  · exact hv

theorem lower_filling (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, r a = h+1 → ∃ x, x < a)
    (hex : ∀ a, r a = h+1 → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (hb : b ∈ onSet P {x | r x ≤ h+1}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  apply carrier_fill P {x | r x ≤ h+1} {x | r x ≤ h}
    (lowerCarrier P r h) (lowerStar P r h) N
    ?_ ?_ ?_ ?_ ?_ (fun _ _ hs hsU ht => lowerCarrier_face P r hr h hs hsU ht)
    (fun _ _ hs hsU ht => lowerStar_face P r hr h hs hsU ht) ?_ ?_ ?_ ?_
    hnN c b hc hcn hcd hca hb hbn hbd
  · intro s _ _
    unfold lowerCarrier
    split_ifs with he
    · exact hne s.1 he
    · exact ⟨s.1,head_mem_vertices P s⟩
  · intro s hs hsU x hx
    have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
    unfold lowerCarrier at hx
    split_ifs at hx with he
    · have hh := hr hx
      change r x ≤ h
      omega
    · have hh := hr.monotone (hs.le_head P hx)
      change r x ≤ h
      omega
  · intro s hs hsU x hx
    unfold lowerStar at hx
    split_ifs at hx with he
    · have hh := hr.monotone hx
      change r x ≤ h+1
      omega
    · exact hsU hx
  · intro s _ _ x hx
    unfold lowerCarrier lowerStar at *
    split_ifs at *
    · exact hx.le
    · exact hx
  · intro s hs _
    unfold lowerStar
    split_ifs
    · exact fun _ hx => hs.le_head P hx
    · exact Set.Subset.rfl
  · intro s hs _ k hk
    unfold lowerCarrier
    split_ifs with he
    · exact hex s.1 he k hk
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro s hs _ k _
    unfold lowerStar
    split_ifs
    · exact exactSet_of_top P (U := Set.Iic s.1) s.1 le_rfl (fun _ hx => hx) k
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro x hx
    change r x ≤ h+1
    change r x ≤ h at hx
    omega
  · intro s _ hsV
    have hsr := hsV (head_mem_vertices P s)
    have he : r s.1 ≠ h+1 := by change r s.1 ≤ h at hsr; omega
    simpa only [lowerStar,ite_eq_right he] using hsV
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma mem_ofPartition {I : Type*} [Fintype I] (p : I → Prefix S)
    (hp : IsPartition p) (i : I) :
    GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ (p i)) ∈ (ofPartition ρ p hp).pieces := by
  classical
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

end Basis
end TwistedBrin

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace Basis

lemma transition_germBrick {B C : Basis ρ} (e : B ≃ C) (b : B) :
    GermBrick.groupEquiv ρ (transitionElement ρ e) b.1 = (e b).1 := by
  rw [← GermBrick.mk_representative ρ b.1,← GermBrick.mk_representative ρ (e b).1]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ _ _) = GermBrick.mk ρ _
  congr 1
  apply LocalEmbedding.ext
  exact transition_chart ρ e b

lemma translate_transition {B C : Basis ρ} (e : B ≃ C) :
    translate ρ (transitionElement ρ e) B = C := by
  classical
  apply Basis.ext
  apply Finset.ext
  intro b
  change b ∈ B.pieces.map (GermBrick.groupEquiv ρ (transitionElement ρ e)).toEmbedding ↔ _
  constructor
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
    change GermBrick.groupEquiv ρ (transitionElement ρ e) a ∈ C.pieces
    rw [transition_germBrick ρ e ⟨a,ha⟩]
    exact (e ⟨a,ha⟩).property
  · intro hb
    obtain ⟨a,ha⟩ := e.surjective ⟨b,hb⟩
    exact Finset.mem_map.mpr ⟨a.1,a.property,(transition_germBrick ρ e a).trans (congrArg Subtype.val ha)⟩

lemma orbit_of_rank_eq {B C : Basis ρ} (hr : rank ρ B = rank ρ C) :
    ∃ g : localGroup ρ, g • B = C := by
  have hc : Fintype.card B = Fintype.card C := by simpa only [rank_eq_card] using hr
  let e := Classical.choice (Fintype.card_eq.mp hc)
  exact ⟨transitionElement ρ e,translate_transition ρ e⟩

end Basis
end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

lemma rank_expand (B : Basis ρ) (P : B → Pattern S) :
    rank ρ (expand ρ B P) = ∑ b : B, Fintype.card (Pattern.Leaves (P b)) := by
  rw [expand,rank_ofChartPartition,Fintype.card_sigma]

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma rectangular_length (b : S →₀ ℕ) (i : Leaves (rectangular b)) (s : S) :
    (leafPrefix (rectangular b) i s).length = b s := by
  classical
  have h := uniform_length (Finsupp.toMultiset b).toList i s
  rw [← Multiset.coe_count,Multiset.coe_toList,Finsupp.count_toMultiset] at h
  exact h

end TwistedBrin.Pattern

namespace TwistedBrin.Prefix
variable {S : Type u}

lemma eq_of_mem_of_length_eq {p q : Prefix S} {x : Box S}
    (hp : x ∈ p.brick) (hq : x ∈ q.brick) (hl : ∀ s, (p s).length = (q s).length) : p = q := by
  apply Prefix.ext
  intro s
  rw [← (mem_brick_iff p x).mp hp s,← (mem_brick_iff q x).mp hq s,hl]

lemma eq_gridPrefix_of_lengths {p : Prefix S} {b : S →₀ ℕ} (hl : ∀ s, (p s).length = b s)
    {x : Box S} (hx : x ∈ p.brick) : p = gridPrefix b (gridPoint b x) :=
  eq_of_mem_of_length_eq hx (mem_gridPrefix b x) (fun s => (hl s).trans (gridPrefix_length _ _ _).symm)

end TwistedBrin.Prefix

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma rectangular_prefix (b : S →₀ ℕ) (i : Leaves (rectangular b)) :
    ∃ z : Prefix.Grid b, leafPrefix (rectangular b) i = Prefix.gridPrefix b z :=
  ⟨_,Prefix.eq_gridPrefix_of_lengths (rectangular_length b i)
    (Prefix.chart_mem_brick _ (fun _ _ => false))⟩

end TwistedBrin.Pattern

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace LocalEmbedding

lemma rectangular_standard (h : LocalEmbedding ρ) :
    ∃ w : S →₀ ℕ, ∀ i : Pattern.Leaves (Pattern.rectangular w),
      ∃ (q : Prefix S) (a : A),
        comp ρ h (ofPrefix ρ (Pattern.leafPrefix (Pattern.rectangular w) i)) =
          comp ρ (ofPrefix ρ q) (global ρ a) := by
  classical
  choose p q a hp he using h.locally_standard
  have hcover : (Set.univ : Set (Box S)) ⊆ ⋃ x, (p x).brick := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hp x⟩
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (p x).brick) (fun x => (p x).isOpen_brick) hcover
  have hc : ∀ x, ∃ i ∈ I, x ∈ (p i).brick := by
    intro x
    simpa only [Set.mem_iUnion,exists_prop] using hI (Set.mem_univ x)
  obtain ⟨w,hw⟩ := finite_grid_refinement I p hc
  refine ⟨w,?_⟩
  intro j
  obtain ⟨z,hz⟩ := Pattern.rectangular_prefix w j
  obtain ⟨x,_,hx⟩ := hw z
  refine ⟨(q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x))),a x,?_⟩
  apply LocalEmbedding.ext
  intro y
  change h ((Pattern.leafPrefix (Pattern.rectangular w) j).chart y) = _
  rw [hz]
  nth_rw 1 [← Prefix.append_suffix hx]
  change h (((p x).append ((p x).suffix (Prefix.gridPrefix w z))).chart y) =
    ((q x).append (((p x).suffix (Prefix.gridPrefix w z)).permute (ρ (a x)))).chart
      (twist ρ (a x) y)
  have he' (x y) : h ((p x).chart y) = (q x).chart (twist ρ (a x) y) := he x y
  rw [Prefix.chart_append,he',twist_chart,← Prefix.chart_append]

end LocalEmbedding
namespace Basis

lemma exists_standard_cut_patterns (B : Basis ρ) :
    ∃ P : B → Pattern S, ∀ i : Σ b : B, Pattern.Leaves (P b),
      ∃ (q : Prefix S) (a : A), expandedChart ρ B P i =
        LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ q) (LocalEmbedding.global ρ a) := by
  choose w hw using fun b : B => LocalEmbedding.rectangular_standard ρ (chart ρ B b)
  exact ⟨fun b => Pattern.rectangular (w b),fun i => hw i.1 i.2⟩

lemma cutRefines_grid_from_patterns (B : Basis ρ) (P : B → Pattern S)
    (q : (Σ b : B, Pattern.Leaves (P b)) → Prefix S)
    (a : (Σ b : B, Pattern.Leaves (P b)) → A)
    (he : ∀ i, expandedChart ρ B P i =
      LocalEmbedding.comp ρ (LocalEmbedding.ofPrefix ρ (q i)) (LocalEmbedding.global ρ (a i)))
    (w : S →₀ ℕ) (hw : ∀ i, (q i).lengths ≤ w) : CutRefines ρ B (grid ρ w) := by
  classical
  let R := fun i : Σ b : B, Pattern.Leaves (P b) =>
    Pattern.rectangular (w - (q i).lengths)
  let Q := fun b : B => Pattern.graft (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
  apply Nonempty.intro
  apply Forest.of_mem ρ Q
  rintro ⟨b,k⟩
  obtain ⟨⟨j,l⟩,rfl⟩ := (Pattern.graftLeaves (P b)
    (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))).surjective k
  obtain ⟨l,rfl⟩ := (Pattern.relabelLeaves (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩)).surjective l
  let i : Σ b : B, Pattern.Leaves (P b) := ⟨b,j⟩
  let r := Pattern.leafPrefix (R i) l
  have hlen : ∀ s, ((q i).append r s).length = w s := by
    intro s
    change ((q i s) ++ (Pattern.leafPrefix (Pattern.rectangular (w - (q i).lengths)) l s)).length = w s
    rw [List.length_append,Pattern.rectangular_length,Finsupp.tsub_apply]
    exact Nat.add_sub_of_le (hw i s)
  obtain ⟨z,hz⟩ : ∃ z : Prefix.Grid w, (q i).append r = Prefix.gridPrefix w z :=
    ⟨_,Prefix.eq_gridPrefix_of_lengths hlen (Prefix.chart_mem_brick _ (fun _ _ => false))⟩
  have hc : GermBrick.mk ρ (expandedChart ρ B Q
      ⟨b,Pattern.graftLeaves (P b)
        (fun j => Pattern.relabel (ρ (a ⟨b,j⟩)⁻¹) (R ⟨b,j⟩))
        ⟨j,Pattern.relabelLeaves (ρ (a i)⁻¹) (R i) l⟩⟩) =
      GermBrick.mk ρ (LocalEmbedding.ofPrefix ρ ((q i).append r)) := by
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
      (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix _ _))) = _
    rw [Pattern.graft_prefix,Pattern.relabel_prefix,LocalEmbedding.ofPrefix_append,
      ← LocalEmbedding.comp_assoc]
    change GermBrick.mk ρ (LocalEmbedding.comp ρ (expandedChart ρ B P i)
      (LocalEmbedding.ofPrefix ρ (r.permute (ρ (a i)⁻¹)))) = _
    rw [he,LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,twist_prefix_inv,
      ← LocalEmbedding.comp_assoc,← LocalEmbedding.ofPrefix_append,GermBrick.mk_gauge]
  rw [hc,hz]
  exact mem_ofPartition ρ _ _ z

end Basis
end TwistedBrin

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma cut_grid_cofinal (B : Basis ρ) :
    ∃ w : S →₀ ℕ, ∀ t, w ≤ t → CutRefines ρ B (grid ρ t) := by
  classical
  obtain ⟨P,hP⟩ := exists_standard_cut_patterns ρ B
  choose q a he using hP
  let w := ∑ i : Σ b : B, Pattern.Leaves (P b), (q i).lengths
  refine ⟨w,fun t ht => cutRefines_grid_from_patterns ρ B P q a he t ?_⟩
  intro i
  exact le_trans (Finset.single_le_sum (f := fun i => (q i).lengths)
    (fun _ _ s => Nat.zero_le _) (Finset.mem_univ i)) ht

theorem cut_directed (B C : Basis ρ) :
    ∃ D : Basis ρ, CutRefines ρ B D ∧ CutRefines ρ C D := by
  obtain ⟨b,hb⟩ := cut_grid_cofinal ρ B
  obtain ⟨c,hc⟩ := cut_grid_cofinal ρ C
  exact ⟨grid ρ (b+c),hb _ (fun s => Nat.le_add_right _ _),
    hc _ (fun s => Nat.le_add_left _ _)⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisTranslateEquiv
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

namespace Merge
variable {ρ} {C : Basis ρ}

lemma rank_lower (m : Merge ρ C) : rank ρ m.lower + 1 = rank ρ C := by
  classical
  rw [lower,rank_ofChartPartition,rank_eq_card]
  have hc := Fintype.card_congr m.leafEquiv
  simp only [Fintype.card_sum,Fintype.card_bool] at hc
  change Fintype.card (Option m.Rest) + 1 = Fintype.card C
  rw [Fintype.card_option]
  omega

lemma lower_cutRefines (m : Merge ρ C) : CutRefines ρ m.lower C := by
  classical
  let P : m.Roots → Pattern S := fun r => match r with
    | none => .split m.coordinate .leaf .leaf
    | some _ => .leaf
  apply cutRefines_ofChartPartition ρ m.rootChart m.rootPartition C P
  intro r j
  cases r with
  | none =>
    cases j with
    | inl j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.left_eq]
    | inr j =>
      simp [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,m.right_eq]
  | some r =>
    simp [P,Pattern.leafPrefix,rootChart,LocalEmbedding.ofPrefix_empty,
      LocalEmbedding.comp_identity,chart_germ]

lemma lower_ne (m : Merge ρ C) : m.lower ≠ C := by
  intro he
  have hr := m.rank_lower
  rw [he] at hr
  omega

end Merge
end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Oligomorphic.finite_palette (h : Oligomorphic ρ) (n : ℕ) :
    ∃ U : Finset S, ∀ F : Finset S, F.card ≤ n →
      ∃ a : A, F.map (ρ a).toEmbedding ⊆ U := by
  classical
  choose R hR using h
  let U := (Finset.range (n+1)).biUnion (fun k => (R k).biUnion id)
  refine ⟨U,fun F hF => ?_⟩
  obtain ⟨E,hE,a,ha⟩ := hR F.card F rfl
  refine ⟨a,?_⟩
  rw [ha]
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨F.card,Finset.mem_range.mpr (by omega),
    Finset.mem_biUnion.mpr ⟨E,hE,hs⟩⟩

end TwistedBrin

namespace TwistedBrin.Pattern
variable {S : Type u}

lemma nodes_add_one (P : Pattern S) : nodes P + 1 = Fintype.card (Leaves P) := by
  induction P with
  | leaf => change 0 + 1 = Fintype.card Unit; simp
  | split s P Q ihP ihQ =>
    change nodes P + nodes Q + 1 + 1 = Fintype.card (Leaves P ⊕ Leaves Q)
    rw [Fintype.card_sum,← ihP,← ihQ]
    omega

lemma depth_le_nodes (P : Pattern S) : depth P ≤ nodes P := by
  induction P with
  | leaf => rfl
  | split s P Q ihP ihQ => simp only [depth,nodes]; omega

lemma coordinates_card_le (P : Pattern S) : (coordinates P).card ≤ nodes P := by
  classical
  induction P with
  | leaf => simp [coordinates,nodes]
  | split s P Q ihP ihQ =>
    have h₁ := Finset.card_insert_le s (coordinates P ∪ coordinates Q)
    have h₂ := Finset.card_union_le (coordinates P) (coordinates Q)
    simp only [coordinates,nodes]
    omega

lemma coordinates_relabel (σ : Equiv.Perm S) (P : Pattern S) :
    coordinates (relabel σ P) = (coordinates P).map σ.toEmbedding := by
  classical
  induction P with
  | leaf => simp [relabel,coordinates]
  | split s P Q ihP ihQ => simp [relabel,coordinates,ihP,ihQ,Finset.map_union]

lemma mem_bounded (U : Finset S) (n : ℕ) (P : Pattern S)
    (hP : coordinates P ⊆ U) (hd : depth P ≤ n) : P ∈ bounded U n := by
  classical
  induction n generalizing P with
  | zero =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q => simp only [depth] at hd; omega
  | succ n ih =>
    cases P with
    | leaf => simp [bounded]
    | split s P Q =>
      have hs : s ∈ U := hP (by simp [coordinates])
      have hP' : coordinates P ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hQ' : coordinates Q ⊆ U := fun x hx => hP (by simp [coordinates,hx])
      have hdP : depth P ≤ n := by simp only [depth] at hd; omega
      have hdQ : depth Q ≤ n := by simp only [depth] at hd; omega
      simp only [bounded,Finset.mem_insert,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inr ⟨s,hs,P,ih P hP' hdP,Q,ih Q hQ' hdQ,rfl⟩

lemma finite_orbit_representatives {A : Type v} [Group A] (ρ : A →* Equiv.Perm S)
    (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Pattern S), ∀ P : Pattern S, Fintype.card (Leaves P) ≤ n →
      ∃ a : A, relabel (ρ a) P ∈ R := by
  classical
  obtain ⟨U,hU⟩ := h.finite_palette ρ n
  refine ⟨bounded U n,fun P hP => ?_⟩
  have hn : nodes P ≤ n := by have := nodes_add_one P; omega
  obtain ⟨a,ha⟩ := hU (coordinates P) ((coordinates_card_le P).trans hn)
  refine ⟨a,mem_bounded U n _ ?_ ?_⟩
  · rwa [coordinates_relabel]
  · rw [depth_relabel]
    exact (depth_le_nodes P).trans hn

end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma translate_twistPieces_expand (B : Basis ρ) (P : B → Pattern S) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) (expand ρ B P) =
      expand ρ B (fun b => Pattern.relabel (ρ (a b)) (P b)) := by
  classical
  apply Basis.ext
  ext c
  change (c ∈ (Finset.univ.image (fun i => GermBrick.mk ρ (expandedChart ρ B P i))).map _) ↔
    c ∈ Finset.univ.image _
  simp only [Finset.mem_map,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,⟨i,rfl⟩,rfl⟩
    exact ⟨⟨i.1,Pattern.relabelLeaves (ρ (a i.1)) (P i.1) i.2⟩,
      (twistPieces_expanded_germ ρ B P a i).symm⟩
  · rintro ⟨⟨b,j⟩,rfl⟩
    obtain ⟨k,rfl⟩ := (Pattern.relabelLeaves (ρ (a b)) (P b)).surjective j
    exact ⟨_,⟨⟨b,k⟩,rfl⟩,twistPieces_expanded_germ ρ B P a ⟨b,k⟩⟩

lemma Forest.expand_eq {B C : Basis ρ} (F : Forest ρ B C) : expand ρ B F.pattern = C := by
  classical
  apply Basis.ext
  ext c
  change c ∈ Finset.univ.image _ ↔ c ∈ C.pieces
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    rw [F.chart_eq]
    exact (F.leaves i).property
  · intro hc
    obtain ⟨i,hi⟩ := F.leaves.surjective ⟨c,hc⟩
    exact ⟨i,(F.chart_eq i).trans (congrArg Subtype.val hi)⟩

lemma Forest.leaves_le_rank {B C : Basis ρ} (F : Forest ρ B C) (b : B) :
    Fintype.card (Pattern.Leaves (F.pattern b)) ≤ rank ρ C := by
  have hr : rank ρ C = ∑ b : B, Fintype.card (Pattern.Leaves (F.pattern b)) :=
    (congrArg (rank ρ) (F.expand_eq ρ)).symm.trans (rank_expand ρ B F.pattern)
  rw [hr]
  exact Finset.single_le_sum (f := fun b : B => Fintype.card (Pattern.Leaves (F.pattern b)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

lemma outgoing_finite_orbit_representatives (h : Oligomorphic ρ) (B : Basis ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ C : Basis ρ, CutRefines ρ B C → rank ρ C ≤ n →
      ∃ a : B → A, translate ρ (twistPiecesHom ρ B a) C ∈ R := by
  classical
  obtain ⟨T,hT⟩ := Pattern.finite_orbit_representatives ρ h n
  let R := (Finset.univ : Finset (B → {P // P ∈ T})).image
    (fun f => expand ρ B (fun b => (f b).val))
  refine ⟨R,fun C hBC hC => ?_⟩
  obtain ⟨F⟩ := hBC
  choose a ha using fun b => hT (F.pattern b) ((F.leaves_le_rank ρ b).trans hC)
  refine ⟨a,?_⟩
  rw [← F.expand_eq ρ,translate_twistPieces_expand]
  exact Finset.mem_image.mpr ⟨fun b => ⟨_,ha b⟩,Finset.mem_univ _,rfl⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinGermBrick
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutInterval.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.GermBrick
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma restricts_iff_chart {b c : GermBrick ρ} (h : LocalEmbedding ρ) (hb : mk ρ h = b) :
    Restricts ρ c b ↔ ∃ p : Prefix S, c = mk ρ (LocalEmbedding.comp ρ h (LocalEmbedding.ofPrefix ρ p)) := by
  constructor
  · rintro ⟨k,p,hk,rfl⟩
    obtain ⟨a,rfl⟩ := (mk_eq_iff ρ k h).mp (hk.symm.trans hb.symm)
    refine ⟨p.permute (ρ a),?_⟩
    rw [LocalEmbedding.comp_assoc,LocalEmbedding.global_ofPrefix,
      ← LocalEmbedding.comp_assoc,mk_gauge]
  · rintro ⟨p,rfl⟩
    exact ⟨h,p,hb.symm,rfl⟩

lemma eq_of_common_restriction_of_region_eq {b c d : GermBrick ρ}
    (hc : Restricts ρ c b) (hd : Restricts ρ d b) (he : region ρ c = region ρ d) : c = d := by
  obtain ⟨p,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hc
  obtain ⟨q,rfl⟩ := (restricts_iff_chart ρ (representative ρ b) (mk_representative ρ b)).mp hd
  have hpq : p.brick = q.brick := by
    change Set.range ((representative ρ b) ∘ p.chart) =
      Set.range ((representative ρ b) ∘ q.chart) at he
    rw [Set.range_comp,Set.range_comp] at he
    exact (Set.image_injective.mpr (representative ρ b).injective) he
  rw [Prefix.brick_injective hpq]

end TwistedBrin.GermBrick

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma mem_descendants (C : Basis ρ) (d : GermBrick ρ) (c : C) :
    c ∈ descendants ρ C d ↔ GermBrick.region ρ c.val ⊆ GermBrick.region ρ d := by
  classical
  simp [descendants]

lemma region_iff_descendants {D C : Basis ρ} (hDC : D ≤ C) (d : D) (x : Box S) :
    x ∈ GermBrick.region ρ d.val ↔
    ∃ c : C, c ∈ descendants ρ C d.val ∧ x ∈ GermBrick.region ρ c.val := by
  constructor
  · intro hx
    obtain ⟨c,hc,_⟩ := C.partition x
    obtain ⟨e,he⟩ := hDC c
    have hxe := GermBrick.region_subset_of_restricts ρ he hc
    have hed : e = d := (D.partition x).unique hxe hx
    subst e
    exact ⟨c,(mem_descendants ρ C d.val c).mpr (GermBrick.region_subset_of_restricts ρ he),hc⟩
  · rintro ⟨c,hc,hx⟩
    exact (mem_descendants ρ C d.val c).mp hc hx

lemma region_eq_of_descendants_eq {D E C : Basis ρ} (hDC : D ≤ C) (hEC : E ≤ C)
    (d : D) (e : E) (he : descendants ρ C d.val = descendants ρ C e.val) :
    GermBrick.region ρ d.val = GermBrick.region ρ e.val := by
  ext x
  rw [region_iff_descendants ρ hDC,region_iff_descendants ρ hEC,he]

lemma germ_eq_of_region_eq_above {B D E : Basis ρ} (hBD : B ≤ D) (hBE : B ≤ E)
    (d : D) (e : E) (he : GermBrick.region ρ d.val = GermBrick.region ρ e.val) : d.val = e.val := by
  obtain ⟨b,hb⟩ := hBD d
  obtain ⟨c,hc⟩ := hBE e
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ d.val
  have hbx := GermBrick.region_subset_of_restricts ρ hb hx
  have hcx := GermBrick.region_subset_of_restricts ρ hc (he ▸ hx)
  have hbc : b = c := (B.partition x).unique hbx hcx
  subst c
  exact GermBrick.eq_of_common_restriction_of_region_eq ρ hb hc he

lemma intervalCode_injective (B C : Basis ρ) :
    Function.Injective (fun D : {D : Basis ρ // B ≤ D ∧ D ≤ C} => intervalCode ρ C D.val) := by
  classical
  have help : ∀ (D E : Basis ρ), B ≤ D → D ≤ C → B ≤ E → E ≤ C →
      intervalCode ρ C D = intervalCode ρ C E → D.pieces ⊆ E.pieces := by
    intro D E hBD hDC hBE hEC he d hd
    have hm : descendants ρ C d ∈ intervalCode ρ C E := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨⟨d,hd⟩,Finset.mem_univ _,rfl⟩
    obtain ⟨e,_,hed⟩ := Finset.mem_image.mp hm
    have hr := region_eq_of_descendants_eq ρ hDC hEC ⟨d,hd⟩ e hed.symm
    have hg := germ_eq_of_region_eq_above ρ hBD hBE ⟨d,hd⟩ e hr
    change d = e.val at hg
    rw [hg]
    exact e.property
  intro D E he
  apply Subtype.ext
  apply Basis.ext
  exact Finset.Subset.antisymm
    (help D.val E.val D.property.1 D.property.2 E.property.1 E.property.2 he)
    (help E.val D.val E.property.1 E.property.2 D.property.1 D.property.2 he.symm)

theorem finite_interval (B C : Basis ρ) : Finite {D : Basis ρ // B ≤ D ∧ D ≤ C} :=
  Finite.of_injective _ (intervalCode_injective ρ B C)

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma rank_rankModel (B : Basis ρ) : rank ρ (rankModel ρ (rank ρ B)) = rank ρ B := by
  classical
  simp only [rankModel,dite_eq_left (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)]
  exact Classical.choose_spec (show ∃ C : Basis ρ, rank ρ C = rank ρ B from ⟨B,rfl⟩)

lemma rank_finite_orbit_representatives (n : ℕ) :
    ∃ R : Finset (Basis ρ), ∀ B : Basis ρ, rank ρ B ≤ n →
      ∃ g : localGroup ρ, translate ρ g B ∈ R := by
  classical
  refine ⟨(Finset.range (n+1)).image (rankModel ρ),fun B hB => ?_⟩
  obtain ⟨g,hg⟩ := orbit_of_rank_eq ρ (rank_rankModel ρ B).symm
  refine ⟨g,Finset.mem_image.mpr ⟨rank ρ B,Finset.mem_range.mpr (by omega),?_⟩⟩
  exact hg.symm

lemma twistPieces_translate_self (B : Basis ρ) (a : B → A) :
    translate ρ (twistPiecesHom ρ B a) B = B := by
  exact MulAction.mem_stabilizer_iff.mp
    (rigid_le_vertexStabilizer ρ B (twistPiecesHom_mem_rigidStabilizer ρ B a))

lemma pair_finite_orbit_representatives (h : Oligomorphic ρ) (n : ℕ) :
    ∃ R : Finset (Basis ρ × Basis ρ), ∀ B C : Basis ρ,
      CutRefines ρ B C → rank ρ C ≤ n →
      ∃ g : localGroup ρ, (translate ρ g B,translate ρ g C) ∈ R := by
  classical
  obtain ⟨T,hT⟩ := rank_finite_orbit_representatives ρ n
  choose Q hQ using fun B : Basis ρ => outgoing_finite_orbit_representatives ρ h B n
  let R := T.biUnion (fun B => (Q B).image (fun C => (B,C)))
  refine ⟨R,fun B C hBC hC => ?_⟩
  have hB : rank ρ B ≤ n := (rank_mono ρ (le_of_cutRefines ρ hBC)).trans hC
  obtain ⟨g,hg⟩ := hT B hB
  obtain ⟨a,ha⟩ := hQ (translate ρ g B) (translate ρ g C)
    (translate_cutRefines ρ g hBC) (by simpa only [rank_translate] using hC)
  refine ⟨twistPiecesHom ρ (translate ρ g B) a * g,?_⟩
  rw [translate_mul,translate_mul,twistPieces_translate_self]
  exact Finset.mem_biUnion.mpr ⟨translate ρ g B,hg,Finset.mem_image.mpr ⟨_,ha,rfl⟩⟩

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutDown.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.Matching.Pair.instPartialOrder _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.instPartialOrderProperCutInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutInterval
variable {ρ} {B C : Basis ρ}
instance instFinite : Finite (CutInterval ρ B C) := by
  let := finite_interval ρ B C
  exact Finite.of_injective
    (fun D : CutInterval ρ B C =>
      (⟨D.val,le_of_cutRefines ρ D.lower,le_of_cutRefines ρ D.upper⟩ :
        {E : Basis ρ // B ≤ E ∧ E ≤ C}))
    (fun _ _ h => ext (congrArg Subtype.val h))

end CutInterval

end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfDirected
attribute [-instance] _root_.OAI.EquivariantOrderChains.simplexAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.OrderChainComplex.instFreeIntSubtypeFinsuppSimplexMemSubmoduleChains _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem exactIn_of_directed [Nonempty P]
    (hdir : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) (n : ℕ) : ExactIn P n := by
  classical
  have hfin (F : Finset P) : ∃ z : P, ∀ x ∈ F, x ≤ z := by
    induction F using Finset.induction_on with
    | empty => exact ⟨Classical.choice ‹Nonempty P›,by simp⟩
    | @insert x F hx ih =>
      obtain ⟨y,hy⟩ := ih
      obtain ⟨z,hxz,hyz⟩ := hdir x y
      exact ⟨z,fun a ha => (Finset.mem_insert.mp ha).elim (fun he => he ▸ hxz)
        (fun haF => (hy a haF).trans hyz)⟩
  intro c hc hn hd ha
  obtain ⟨z,hz⟩ := hfin (vertexSupport P c)
  have hcz : c ∈ carrier P z := fun s hs => ⟨hc hs,fun x hx =>
    hz x ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)⟩
  refine ⟨cone P z c,carrier_le_module P z (cone_carrier P z hcz),
    cone_mem_degreeModule P z hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
theorem lower_filling_many (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (k : ℕ) (b : Chain P)
    (hb : b ∈ onSet P {x | r x ≤ h+k}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  induction k generalizing b with
  | zero => exact ⟨b,by simpa only [Nat.add_zero] using hb,hbn,hbd⟩
  | succ k ih =>
    obtain ⟨b',hb',hbn',hbd'⟩ := lower_filling P r hr (h+k) N
      (fun a ha => hne a (by omega))
      (fun a ha => hex a (by omega)) hnN c b
      (onSet_mono P (fun x hx => by change r x ≤ h+k; change r x ≤ h at hx; omega) hc)
      hcn hcd hca (by simpa only [Nat.add_assoc] using hb) hbn hbd
    exact ih b' hb' hbn' hbd'

theorem exactSet_sublevel (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (hall : ExactIn P n) :
    ExactSet P {x | r x ≤ h} n := by
  classical
  intro c hc hn hd ha
  obtain ⟨b,hb,hbn,hbd⟩ := hall c (onSet_le_module P _ hc) hn hd ha
  let k := (vertexSupport P b).sup r
  have hb' : b ∈ onSet P {x | r x ≤ h+k} := by
    intro s hs
    refine ⟨hb hs,fun x hx => ?_⟩
    have hxr : r x ≤ k := Finset.le_sup ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)
    change r x ≤ h+k
    omega
  exact lower_filling_many P r hr h N hne hex hnN c hc hn hd ha k b hb' hbn hbd
end

open OrderListChains
end OrderChains

universe u v

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutBasis
lemma strictMono_rank : StrictMono (fun B : CutBasis ρ => rank ρ B.val) := by
  intro B C h
  apply rank_strictMono ρ
  exact lt_of_le_of_ne (le_of_cutRefines ρ h.le) (fun he => h.ne (ext he))
lemma directed (B C : CutBasis ρ) : ∃ D, B ≤ D ∧ C ≤ D := by
  obtain ⟨D,hBD,hCD⟩ := cut_directed ρ B.val C.val
  exact ⟨⟨D⟩,hBD,hCD⟩
lemma lower_nonempty [Nonempty S] (C : CutBasis ρ) (h : 2 ≤ rank ρ C.val) :
    ∃ B : CutBasis ρ, B < C := by
  let M := groundMatching C.val (Classical.choice ‹Nonempty S›) 1 (by simpa using h)
  let e := M.edge 0
  exact ⟨⟨e.lower⟩,lt_of_le_of_ne e.lower_cutRefines (fun he => e.lower_ne (congrArg CutBasis.val he))⟩

theorem sublevel_exact [Nonempty S] (n h : ℕ) (hh : 2*(2*2^(n+2)+1) ≤ h) :
    ExactSet (CutBasis ρ) {B | rank ρ B.val ≤ h} n := by
  apply exactSet_sublevel (CutBasis ρ) (fun B => rank ρ B.val) strictMono_rank h n
    (fun C hC => lower_nonempty C (by omega)) ?_ le_rfl
    (exactIn_of_directed (CutBasis ρ) directed n)
  intro C hC k hk
  apply lower_exactSet C k
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hk 2)
  omega
end CutBasis
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ActionTransport
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace ActionTransport

universe u v w
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

lemma finite_orbits_of_cover (T : Set X) (hT : T.Finite)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ T) : Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let : Finite T := hT.to_subtype
  apply Finite.of_surjective (fun x : T => (⟦x.val⟧ : MulAction.orbitRel.Quotient G X))
  intro q
  obtain ⟨g,hg⟩ := hcov q.out
  exact ⟨⟨g • q.out,hg⟩,by simp only [MulAction.orbitRel.Quotient.quotient_smul_eq,Quotient.out_eq]⟩

lemma finite_orbits_of_map {Y : Type w} [MulAction G Y]
    [Finite (MulAction.orbitRel.Quotient G Y)] (f : X → Y)
    (heq : ∀ (g : G) x, f (g • x) = g • f x) (hfin : ∀ y, Finite {x // f x = y}) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let F := orbitFrames G Y
  let : Finite F.Index := inferInstanceAs (Finite (MulAction.orbitRel.Quotient G Y))
  let (i : F.Index) : Finite {x // f x = F.rep i} := hfin _
  have hs : Function.Surjective (fun z : Σ i : F.Index, {x // f x = F.rep i} =>
      (⟦z.2.val⟧ : MulAction.orbitRel.Quotient G X)) := by
    intro q
    let x := q.out
    let g := F.element (f x)
    have hf : f (g⁻¹ • x) = F.rep (F.index (f x)) := by
      rw [heq,inv_smul_eq_iff]
      exact (F.frame (f x)).symm
    refine ⟨⟨F.index (f x),⟨g⁻¹ • x,hf⟩⟩,?_⟩
    simp only [MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact Quotient.out_eq q
  exact Finite.of_surjective _ hs
end ActionTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.sublevel_covariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
lemma sublevel_val_injective (h : ℕ) : Function.Injective (fun B : Sublevel (ρ := ρ) h => B.val.val) := by
  intro B C he
  exact Subtype.ext (ext he)
lemma edge_finite_orbits (ho : Oligomorphic ρ) (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Edge (Sublevel (ρ := ρ) h))) := by
  classical
  obtain ⟨R,hR⟩ := pair_finite_orbit_representatives ρ ho h
  let f : Edge (Sublevel (ρ := ρ) h) → Basis ρ × Basis ρ := fun e => (e.val.1.val.val,e.val.2.val.val)
  have hi : Function.Injective f := by
    intro e d he
    apply Subtype.ext
    exact Prod.ext (sublevel_val_injective h (congrArg Prod.fst he))
      (sublevel_val_injective h (congrArg Prod.snd he))
  apply finite_orbits_of_cover (f ⁻¹' (R : Set (Basis ρ × Basis ρ))) (R.finite_toSet.preimage hi.injOn)
  intro e
  exact hR _ _ e.property e.val.2.property
end TwistedBrin.Basis.CutBasis

namespace FiniteExtension
variable {L : Type*} [Group L] (K : Subgroup L) [K.Normal]
lemma finitelyGenerated [Finite (L ⧸ K)] [Group.FG K] : Group.FG L := by
  classical
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  let T : Set L := K.subtype '' S ∪ Set.range (sectionMap K)
  have ht : T.Finite := (hfin.image _).union (Set.finite_range _)
  have hK (k : K) : (k : L) ∈ Subgroup.closure T := by
    have hk : k ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hk using Subgroup.closure_induction with
    | mem k hk => exact Subgroup.subset_closure (Or.inl ⟨k,hk,rfl⟩)
    | one => exact (Subgroup.closure T).one_mem
    | mul k l hk hl ik il => exact (Subgroup.closure T).mul_mem ik il
    | inv k hk ik => exact (Subgroup.closure T).inv_mem ik
  have htop : Subgroup.closure T = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    have ht := (Subgroup.closure T).mul_mem (hK (factor K x))
      (Subgroup.subset_closure (Or.inr ⟨pi K x,rfl⟩))
    simpa only [factor,mul_assoc,inv_mul_cancel,mul_one] using ht
  exact Group.fg_iff.mpr ⟨T,htop,ht⟩
end FiniteExtension

namespace TwistedBrin.Basis
open ActionPresentation
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
lemma pair_finitelyGenerated (hρ : Function.Injective ρ)
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) {B C : Basis ρ}
    (hBC : CutRefines ρ B C) : Group.FG (pairStabilizer ρ B C) := by
  let F := hBC.some
  let (b : B) : Group.FG (pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) := hS _
  let e := F.pairKernelEquiv ρ hρ
  let : Group.FG (pairPermutationHom ρ B C).ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let := (pairPermutationHom ρ B C).ker.fintypeQuotientOfFiniteIndex
  exact FiniteExtension.finitelyGenerated (pairPermutationHom ρ B C).ker
end TwistedBrin.Basis

namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
lemma sublevel_vertex_stabilizer (h : ℕ) (B : Sublevel (ρ := ρ) h) :
    MulAction.stabilizer (localGroup ρ) B = vertexStabilizer ρ B.val.val := by
  ext g
  change (g • B = B) ↔ translate ρ g B.val.val = B.val.val
  exact ⟨fun he => congrArg (fun C : Sublevel (ρ := ρ) h => C.val.val) he,
    fun he => sublevel_val_injective h he⟩
lemma sublevel_edge_stabilizer (h : ℕ) (e : Edge (Sublevel (ρ := ρ) h)) :
    MulAction.stabilizer (localGroup ρ) e = pairStabilizer ρ e.val.1.val.val e.val.2.val.val := by
  ext g
  change (g • e = e) ↔ g ∈ vertexStabilizer ρ e.val.1.val.val ∧ g ∈ vertexStabilizer ρ e.val.2.val.val
  rw [← sublevel_vertex_stabilizer h e.val.1,← sublevel_vertex_stabilizer h e.val.2]
  change (g • e = e) ↔ (g • e.val.1 = e.val.1) ∧ (g • e.val.2 = e.val.2)
  exact ⟨fun he => ⟨congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.1) he,
    congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.2) he⟩,
    fun he => Subtype.ext (Prod.ext he.1 he.2)⟩

end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace FiniteIndexProducts
variable {G : Type} [Group G] (K : Subgroup G) [K.Normal] [K.FiniteIndex]
variable (I : Type) (n : ℕ)

lemma downNormal (hz : IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ K I) n) := hz.of_iso (homologyIso K I n)
lemma upNormal (hz : IsZero (groupHomology (RegularProductR.rep ℤ K I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) n) := hz.of_iso (homologyIso K I n).symm

variable (H : Subgroup G) [H.FiniteIndex]
include H in

theorem down (hz : IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ H I) n) := by
  let C := H.normalCore
  have hC := downNormal C I n hz
  let e : C.subgroupOf H ≃* C := Subgroup.subgroupOfEquivOfLe H.normalCore_le
  have hcH := hC.of_iso (RegularProductR.homologyRelabel e I n)
  exact upNormal (C.subgroupOf H) I n hcH

end FiniteIndexProducts

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] {n : ℕ}

lemma tuple_injective : Function.Injective (tuple (P := P) (n := n)) := by
  intro s t he
  have hl : s.val.1 :: s.val.2 = t.val.1 :: t.val.2 := by
    apply List.ext_get
    · simp only [List.length_cons,show s.val.2.length = n from s.property.2,
        show t.val.2.length = n from t.property.2]
    · intro i hi hj
      have hi' : i < n+1 := by
        have hs : s.val.2.length = n := s.property.2
        simpa only [List.length_cons,hs] using hi
      exact congrFun he ⟨i,hi'⟩
  exact Subtype.ext (Prod.ext (List.cons.inj hl).1 (List.cons.inj hl).2)

lemma tuple_smul (g : G) (s : simplexSet P n) (i : Fin (n+1)) :
    tuple (g • s) i = g • tuple s i := by
  have hi : i.val < (s.val.1 :: s.val.2).length := by
    have hs : s.val.2.length = n := s.property.2
    simpa only [List.length_cons,hs] using i.isLt
  have hi' : i.val < ((s.val.1 :: s.val.2).map (fun x : P => g • x)).length := by simpa using hi
  change ((s.val.1 :: s.val.2).map (fun x : P => g • x))[i.val] = g • (s.val.1 :: s.val.2)[i.val]
  exact List.getElem_map (fun x : P => g • x)

lemma endpoints_smul (g : G) (s : simplexSet P n) :
    endpoints (g • s) = g • endpoints s := by
  apply Subtype.ext
  exact Prod.ext (tuple_smul g s _) (tuple_smul g s _)
end EquivariantOrderChains

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

lemma simplex_endpoint_fiber_finite (h n : ℕ) (e : Edge (Sublevel (ρ := ρ) h)) :
    Finite {s : simplexSet (Sublevel (ρ := ρ) h) n // endpoints s = e} := by
  classical
  let B := e.val.1.val.val
  let C := e.val.2.val.val
  let := finite_interval ρ B C
  let j : {s : simplexSet (Sublevel (ρ := ρ) h) n // endpoints s = e} →
      (Fin (n+1) → {D : Basis ρ // B ≤ D ∧ D ≤ C}) := fun s i =>
    ⟨(tuple s.val i).val.val,by
      have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1.val.val) s.property
      have hc := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2.val.val) s.property
      change (tuple s.val (Fin.last n)).val.val = B at hb
      change (tuple s.val 0).val.val = C at hc
      rw [← hb,← hc]
      exact ⟨le_of_cutRefines ρ (tuple_antitone s.val (Fin.le_last i)),
        le_of_cutRefines ρ (tuple_antitone s.val (Fin.zero_le i))⟩⟩
  apply Finite.of_injective j
  intro s t he
  apply Subtype.ext
  apply tuple_injective
  funext i
  apply sublevel_val_injective h
  exact congrArg Subtype.val (congrFun he i)

lemma simplex_finite_orbits (ho : Oligomorphic ρ) (h n : ℕ) :
    Finite (OrbitCoefficients.Orbits (G := localGroup ρ) (simplexSet (Sublevel (ρ := ρ) h) n)) := by
  let := edge_finite_orbits ho h
  exact finite_orbits_of_map endpoints endpoints_smul (simplex_endpoint_fiber_finite h n)
end TwistedBrin.Basis.CutBasis

namespace FiniteFiberStabilizers
universe u v w
variable {G : Type u} [Group G] {X : Type v} {Y : Type w}
  [MulAction G X] [MulAction G Y]
variable (f : X → Y) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)

include heq
lemma stabilizer_le (x : X) : MulAction.stabilizer G x ≤ MulAction.stabilizer G (f x) := by
  intro g hg
  change g • f x = f x
  rw [← heq, show g • x = x from hg]

lemma finiteIndex (x : X) [Finite {z : X // f z = f x}] :
    ((MulAction.stabilizer G x).subgroupOf (MulAction.stabilizer G (f x))).FiniteIndex := by
  classical
  let H := MulAction.stabilizer G (f x)
  let K := MulAction.stabilizer H x
  have hfin : Finite (MulAction.orbit H x) := by
    let j : MulAction.orbit H x → {z : X // f z = f x} := fun z => ⟨z.val,by
      obtain ⟨g,hg⟩ := z.property
      rw [← hg]
      change f (g.val • x) = f x
      rw [heq]
      exact g.property⟩
    exact Finite.of_injective j (fun a b h => Subtype.ext (congrArg (fun z : {z : X // f z = f x} => z.val) h))
  let := hfin
  let : Finite (H ⧸ K) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer H x)
  have hK : K = (MulAction.stabilizer G x).subgroupOf H := by
    ext g
    rfl
  rw [← hK]
  exact Subgroup.finiteIndex_iff.mpr Subgroup.index_ne_zero_of_finite
end FiniteFiberStabilizers

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

lemma simplex_stabilizer_fg (hρ : Function.Injective ρ)
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F))
    (h n : ℕ) (s : simplexSet (Sublevel (ρ := ρ) h) n) :
    Group.FG (MulAction.stabilizer (localGroup ρ) s) := by
  let f : simplexSet (Sublevel (ρ := ρ) h) n → Edge (Sublevel (ρ := ρ) h) := endpoints
  let H := MulAction.stabilizer (localGroup ρ) (f s)
  let K := MulAction.stabilizer (localGroup ρ) s
  let := simplex_endpoint_fiber_finite h n (f s)
  let : (K.subgroupOf H).FiniteIndex := FiniteFiberStabilizers.finiteIndex f endpoints_smul s
  let eH := MulEquiv.subgroupCongr (sublevel_edge_stabilizer (ρ := ρ) h (f s))
  let := pair_finitelyGenerated ρ hρ hS (f s).property
  let : Group.FG H := Group.fg_of_surjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let : Group.FG (K.subgroupOf H) := Subgroup.fg_of_index_ne_zero _
  let e := Subgroup.subgroupOfEquivOfLe (FiniteFiberStabilizers.stabilizer_le (G := localGroup ρ) f endpoints_smul s)
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

lemma simplex_stabilizer_products (hρ : Function.Injective ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    (h n : ℕ) (s : simplexSet (Sublevel (ρ := ρ) h) n) (I : Type) (j : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer (localGroup ρ) s) I) (j+1)) := by
  let f : simplexSet (Sublevel (ρ := ρ) h) n → Edge (Sublevel (ρ := ρ) h) := endpoints
  let H := MulAction.stabilizer (localGroup ρ) (f s)
  let K := MulAction.stabilizer (localGroup ρ) s
  let := simplex_endpoint_fiber_finite h n (f s)
  let : (K.subgroupOf H).FiniteIndex := FiniteFiberStabilizers.finiteIndex f endpoints_smul s
  let eH := MulEquiv.subgroupCongr (sublevel_edge_stabilizer (ρ := ρ) h (f s))
  have hh : IsZero (groupHomology (RegularProductR.rep ℤ H I) (j+1)) :=
    CategoryTheory.Limits.IsZero.of_iso (pair_regular_products hρ hFP hz (f s).property I j)
      (RegularProductR.homologyRelabel eH I (j+1))
  have hk := FiniteIndexProducts.down I (j+1) (K.subgroupOf H) hh
  let e := Subgroup.subgroupOfEquivOfLe (FiniteFiberStabilizers.stabilizer_le (G := localGroup ρ) f endpoints_smul s)
  exact hk.of_iso (RegularProductR.homologyRelabel e I (j+1)).symm
end TwistedBrin.Basis.CutBasis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactSubtypeOfExactSet
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChains
open OrderListChains
variable (P : Type*) [Preorder P]
lemma exactSubtype_of_exactSet {U : Set P} (u : U) {n : ℕ} (he : ExactSet P U n) :
    ExactIn U n := by
  intro c hc hn hd ha
  have hcU : c ∈ onSet U Set.univ := fun s hs => ⟨hc hs,Set.subset_univ _⟩
  have hi := map_onSet U (fun x : U => x.val) (V := U)
    (fun x _ => x.property) (fun _ _ _ _ hxy => hxy) hcU
  have hid : boundary P (mapChain U (fun x : U => x.val) c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hia : augmentation P (mapChain U (fun x : U => x.val) c) = 0 := by
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdU,hdn,hdd⟩ := he _ hi (map_degree U _ hn) hid hia
  have hp := map_onSet P (project P U u) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (project P U u x).val ≤ (project P U u y).val
      simpa only [project_val P u hx,project_val P u hy] using hxy) hdU
  refine ⟨mapChain P (project P U u) d,onSet_le_module U _ hp,map_degree P _ hdn,?_⟩
  rw [boundary_mapChain,hdd,mapChain_comp]
  have hf : project P U u ∘ (fun x : U => x.val) = id := funext (project_include P u)
  rw [hf,mapChain_id]
end OrderChains

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

theorem localGroup_regular_products [Nonempty S] (hρ : Function.Injective ρ)
    (ho : Oligomorphic ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    (I : Type) (N : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (localGroup ρ) I) (N+1)) := by
  let h := 2*(2*2^(N+1+2)+1)
  let P := Sublevel (ρ := ρ) h
  have ht : 1 ≤ h := by dsimp [h]; omega
  let u : P := ⟨⟨trivial ρ⟩,by
    change rank ρ (trivial ρ) ≤ h
    simpa only [rank,trivial,Finset.card_singleton] using ht⟩
  let : Nonempty P := ⟨u⟩
  apply OrderBrown.vanishing (G := localGroup ρ) (P := P) N
  · intro i hi
    apply OrderChains.exactSubtype_of_exactSet (CutBasis ρ) u
    apply sublevel_exact i h
    dsimp [h]
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hi 2)
    omega
  · exact simplex_finite_orbits ho h
  · intro n s
    apply simplex_stabilizer_fg hρ _ h n s
    intro F
    let := hFP F
    exact ActionPresentation.fg_of_fp
  · exact simplex_stabilizer_products hρ hFP hz h

theorem localGroup_geometric_of_certificates_oai [Nonempty S]
    (hρ : Function.Injective ρ) (ho : Oligomorphic ρ)
    [Group.IsFinitelyPresented A]
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1))) :
    SimpleFInftyOvergroups.HasTypeFInfty (localGroup ρ) := by
  let := localGroup_finitelyPresented hρ ho (fun F => by
    let := hFP F
    exact ActionPresentation.fg_of_fp)
  apply SimpleFInftyOvergroups.geometric_product_criterion
  intro I n hn
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact localGroup_regular_products hρ ho hFP hz I j
end TwistedBrin.Basis.CutBasis

end
end

end OAI
end

theorem solution : type_of% @OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates_oai := @OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates_oai
