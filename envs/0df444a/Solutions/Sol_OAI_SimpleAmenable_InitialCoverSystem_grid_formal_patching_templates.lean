-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:00:02.197995+00:00
-- url     : https://prove2.me/submissions/e9890092-dfea-4234-bc0f-9724e22c33f6

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa011
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_actual_template_word_controls
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_gridInputs_normalize

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullSectorSupport
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_supported (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (B.fullGeometricSector hlarge P h V) := by
  intro I
  let b := smallAlphabetBalance hlarge I.val (by have hh := I.property.2; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  rw [B.fullGeometricSector_inclusion hlarge P h I.val I.property.1 b hb (h _ (by have hh := I.property.2; omega) b hb) V hV]
  rintro x ⟨t,rfl⟩
  exact B.geometricSector_aligned I.val b hb P _ V t

end InitialCoverSystem
end FullSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteSectorPartition
namespace ActualLawfulTable
variable {E H Q Ω κ : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_range_le_biUnion (W : κ → Set Ω) (S : Finset κ)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hd : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hdisjoint (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j) = W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he,T.sector_union hd]
    rintro x ⟨s,rfl⟩
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set Ω) (V : Set Ω)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j))
    (hcover : ∀ ω, ω ∈ V ↔ ∃ i, ω ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V = ⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext ω
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hcover ω
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hdisjoint _
    (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Fintype κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_partition_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (W : κ → polygonAlgebra a)
    (hW : ∀ i, ResolvedBy (fun z => (primitiveTests (a := a) (r := r) P z).val) (W i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (W i).val (W j).val)
    (hcover : ∀ p, p ∈ V.val ↔ ∃ i, p ∈ (W i).val) :
    (B.fullGeometricSector hlarge P h V).range ≤
      ⨆ i, (B.fullGeometricSector hlarge P h (W i)).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_range_le_partition
  · intro i j hij
    exact resolvedPolygonMask_disjoint _ (hW i) (hdisjoint hij)
  · intro ω
    constructor
    · rintro ⟨p,hp,hpV⟩
      obtain ⟨i,hi⟩ := (hcover p).mp hpV
      exact ⟨i,p,hp,hi⟩
    · rintro ⟨i,p,hp,hi⟩
      exact ⟨p,hp,(hcover p).mpr ⟨i,hi⟩⟩

end InitialCoverSystem

end FiniteSectorPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InvariantPatching
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InvariantPatching
variable {G D α ι : Type*} [Group G] [Group D]

theorem sameActionOn_free_lift (P : Subgroup G) (f g : α → G)
    (hf : ∀ i, f i ∈ (Subgroup.normalizer (P : Set G))) (hg : ∀ i, g i ∈ (Subgroup.normalizer (P : Set G)))
    (h : SameActionOn f g P) :
    SameActionOn (FreeGroup.lift f) (FreeGroup.lift g) P := by
  let F : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨f i,hf i⟩)
  let J : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨g i,hg i⟩)
  have hF : (Subgroup.normalizer (P : Set G)).subtype.comp F = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro i
    simp [F]
  have hJ : (Subgroup.normalizer (P : Set G)).subtype.comp J = FreeGroup.lift g := by
    apply FreeGroup.ext_hom
    intro i
    simp [J]
  have he : P.normalizerMonoidHom.comp F = P.normalizerMonoidHom.comp J := by
    apply FreeGroup.ext_hom
    intro i
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simpa [F,J] using h i x.val x.property
  intro w x hx
  have hh := congrArg (fun k : FreeGroup α →* MulAut P => ((k w) ⟨x,hx⟩).val) he
  change (F w).val*x*(F w).val⁻¹ = (J w).val*x*(J w).val⁻¹ at hh
  have hf' : (F w).val = FreeGroup.lift f w := DFunLike.congr_fun hF w
  have hg' : (J w).val = FreeGroup.lift g w := DFunLike.congr_fun hJ w
  simpa only [hf',hg'] using hh

theorem normalizes_of_same_action (P : Subgroup G) (x y : G)
    (hx : x ∈ (Subgroup.normalizer (P : Set G))) (h : ∀ z ∈ P, x*z*x⁻¹=y*z*y⁻¹) :
    y ∈ (Subgroup.normalizer (P : Set G)) := by
  intro z
  constructor
  · intro hz
    rw [← h z hz]
    exact (hx z).mp hz
  · intro hz
    have hu : x⁻¹*(y*z*y⁻¹)*x ∈ P := by
      have hu' := ((Subgroup.normalizer (P : Set G)).inv_mem hx (y*z*y⁻¹)).mp hz
      rw [inv_inv] at hu'
      exact hu'
    have hh := h _ hu
    have he : x*(x⁻¹*(y*z*y⁻¹)*x)*x⁻¹ = y*z*y⁻¹ := by group
    rw [he] at hh
    have hv : z=x⁻¹*(y*z*y⁻¹)*x := by
      have ht := congrArg (fun q => y⁻¹*q*y) hh
      simpa only [mul_assoc,inv_mul_cancel,inv_mul_cancel_left,mul_inv_cancel_left,mul_one] using ht
    rwa [← hv] at hu

theorem patching_centrality (f : α → G) (P : ι → Subgroup G)
    (hgen : (FreeGroup.lift f).range ≤ ⨆ i, P i)
    (hinv : ∀ i j, f j ∈ (Subgroup.normalizer (P i : Set G)))
    (w : FreeGroup α)
    (hlocal : ∀ i, ∃ g : α → G, SameActionOn f g (P i) ∧
      FreeGroup.lift g w ∈ Subgroup.centralizer (P i : Set G)) :
    ∀ x ∈ (FreeGroup.lift f).range, Commute (FreeGroup.lift f w) x := by
  have hc : ∀ i, FreeGroup.lift f w ∈ Subgroup.centralizer (P i : Set G) := by
    intro i
    obtain ⟨g,hg,hgw⟩ := hlocal i
    have hact := sameActionOn_free_lift (P i) f g (hinv i)
      (fun j => normalizes_of_same_action (P i) _ _ (hinv i j) (hg j)) hg
    intro x hx
    have he := hact w x hx
    have he' : FreeGroup.lift g w*x*(FreeGroup.lift g w)⁻¹=x := by
      rw [← hgw x hx]; group
    rw [he'] at he
    have ht := congrArg (fun z => z*FreeGroup.lift f w) he
    exact (by simpa only [mul_assoc,inv_mul_cancel,mul_one] using ht :
      FreeGroup.lift f w*x=x*FreeGroup.lift f w).symm
  have hs : (⨆ i, P i) ≤ Subgroup.centralizer {FreeGroup.lift f w} := by
    apply iSup_le
    intro i x hx y hy
    obtain rfl : y=FreeGroup.lift f w := Set.mem_singleton_iff.mp hy
    exact (hc i x hx).symm
  intro x hx
  exact show FreeGroup.lift f w*x=x*FreeGroup.lift f w from hs (hgen hx) _ rfl

end InvariantPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_IndividualGridSplits
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IndividualGridSplits
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    {ι D : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 15 < m+1)
    (Q : (i : ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : ι → polygonAlgebra a) (W : D → polygonAlgebra a)

theorem gridPiece_supported
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (d : D) (i : ι) : B.AlignedSmallSupported (B.gridPiece hlarge Q h U W d i) := by
  apply B.fullGeometricSector_supported
  intro x y he
  exact and_congr (hU i x y he) (hW i d x y he)

theorem gridPieces_generate [Fintype D]
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val) :
    (⨆ i, (B.gridInput hlarge Q h U i).range) ≤
      ⨆ d, ⨆ i, (B.gridPiece hlarge Q h U W d i).range := by
  apply iSup_le
  intro i
  have hle := B.fullGeometricSector_partition_range hlarge (Q i) (h i) (U i)
    (fun d => U i ⊓ W d)
    (fun d x y he => and_congr (hU i x y he) (hW i d x y he))
    (fun d e hde => (hdisjoint hde).mono (fun _ hx => hx.2) (fun _ hx => hx.2))
    (fun x => by
      constructor
      · intro hx
        obtain ⟨d,hd⟩ := hcover x
        exact ⟨d,hx,hd⟩
      · rintro ⟨d,hd⟩; exact hd.1)
  exact hle.trans (iSup_mono fun d => le_iSup (fun i => (B.gridPiece hlarge Q h U W d i).range) i)

end InitialCoverSystem
end IndividualGridSplits

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallStarRelators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallStarRelators
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

theorem smallFamilyStarWord_eval (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val))) :
    (copyFamilyEval F).comp smallFamilyStarWord=smallFamilyEval f := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  have h := DFunLike.congr_fun (hspec I i)
    (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
  simpa only [MonoidHom.comp_apply,smallFamilyStarWord,FreeGroup.lift_apply_of,
    copyFamilyEval_of,smallFamilyEval_of,alphabetStarLift,
    Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using h

end SmallStarRelators

section CellConstantActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem cell_restrict_action (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  exact B.chart_action_transfer hlarge P h U (U ⊓ W) W hU
    (fun x y hh => and_congr (hU x y hh) (hW x y hh)) hW
    (by rw [inf_assoc,inf_idem]) f hf hc I s

end InitialCoverSystem
end CellConstantActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallFormalGlobal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallFormalGlobal
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω] [Group H]

theorem smallFamily_assignment_law
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hlaw : ∀ S : Finset α, S.card≤15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel U w=1 → ∀ v ∈ smallFamilyLocal (ι := ι) S,
      Commute (smallFamilyEval F w) (smallFamilyEval F v))
    (hα : 5≤Fintype.card α) :
    HasCentralLaw (smallFamilyModel U) (smallFamilyEval F).rangeRestrict := by
  classical
  let e := smallFamilyEval F
  let v := smallFamilyModel (α := α) U
  let : Group.IsPerfect e.range := smallFamilyEval_perfect F
  obtain ⟨E,_hEsub,hE⟩ := Finset.exists_subset_card_eq
    (show 5≤(Finset.univ : Finset α).card by simpa using hα)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<E.card by omega)
  obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_ne (show 1<E.card by omega) x
  let a : SwapLabel α := ⟨Equiv.swap x y,x,y,Ne.symm hyx,rfl⟩
  have ha : a.val.support⊆E := by
    change (Equiv.swap x y).support⊆E
    rw [Equiv.Perm.support_swap (Ne.symm hyx)]
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  refine small_support_assignment_law (smallFamilyLocal (ι := ι)) smallFamilyLocal_mono
    v e.rangeRestrict e.rangeRestrict_surjective smallFamilyLocal_generate
    (smallFamilyModel_support U) ?_ E hE a ha ?_
  · intro S hS d hd hv z hz
    apply Commute.of_map (f := e.range.subtype) Subtype.val_injective
    exact hlaw S hS d hd hv z hz
  · intro S hS _ g hg
    exact smallFamilyModel_complete U hsep S hS g hg

end SmallFormalGlobal

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SupportedCellPatching
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SupportedCellPatching
variable {α ι D H : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem supported_cell_patching
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (P : D → Subgroup H)
    (hgen : (copyFamilyEval F).range ≤ ⨆ d, P d)
    (hinv : ∀ d i s, F i s ∈ Subgroup.normalizer (P d : Set H))
    (G : D → Option ι → TrackStar α →* H)
    (hact : ∀ d (I : FiveAlphabet α) i s,
      ∀ x ∈ P d,
        F i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        G d i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (G d i (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    (hlocal : ∀ d (S : Finset α), S.card ≤ 15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}) w=1 →
      ∀ x ∈ P d, Commute (copyFamilyEval (G d) (smallFamilyStarWord w)) x)
    (hα : 5 ≤ Fintype.card α) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  classical
  let f₀ : SmallFamilyLabel α ι → H := fun l => f l.1 l.2.1 l.2.2
  have hfs (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
      f I i s=F i (alphabetStarLift I s) := by
    have hh := DFunLike.congr_fun (hspec I i)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
    simpa only [MonoidHom.comp_apply,alphabetStarLift,
      Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using hh.symm
  have hgen' : (FreeGroup.lift f₀).range ≤ ⨆ d, P d := by
    rintro x ⟨w,rfl⟩
    apply hgen
    refine ⟨smallFamilyStarWord w,?_⟩
    exact DFunLike.congr_fun (smallFamilyStarWord_eval F f hspec) w
  apply smallFamily_assignment_law _ ?_ f ?_ hα
  · intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  · intro S hS w hw hrel v _hv
    have hc := patching_centrality f₀ P hgen' (fun d l => by
      rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
      exact hinv _ _ _) w ?_
    · exact hc _ ⟨v,rfl⟩
    · intro d
      let g : SmallFamilyLabel α ι → H := fun l => G d l.2.1 (alphabetStarLift l.1 l.2.2)
      have hg : (FreeGroup.lift g)=(copyFamilyEval (G d)).comp smallFamilyStarWord := by
        apply FreeGroup.ext_hom
        rintro ⟨I,i,s⟩
        simp [g,smallFamilyStarWord]
      refine ⟨g,?_,?_⟩
      · intro l x hx
        rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
        exact hact d l.1 l.2.1 _ x hx
      · rw [hg]
        intro x hx
        exact (hlocal d S hS w hw hrel x hx).eq.symm

end SupportedCellPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GridFormalPatching
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GridFormalPatching

theorem inner_action_iSup {G J : Type*} [Group G] (P : J → Subgroup G) (x y : G)
    (h : ∀ j, ∀ z ∈ P j, x*z*x⁻¹=y*z*y⁻¹) :
    ∀ z ∈ ⨆ j, P j, x*z*x⁻¹=y*z*y⁻¹ := by
  have hh : (⨆ j, P j) ≤ MonoidHom.eqLocus (MulAut.conj x).toMonoidHom
      (MulAut.conj y).toMonoidHom := by
    apply iSup_le
    intro j z hz
    exact h j z hz
  exact hh

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    {τ : D → Type*} [∀ d, Finite (τ d)]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem grid_formal_patching (hlarge : 25 ≤ m+1)
    (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
      B.fullGeometricSector (by omega) (Q none) (h none) (W d))
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (T : (d : D) → τ d → Fin 5 × (CutRing × CutRing))
    (hT : ∀ d I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (T d))
    (V : D → polygonAlgebra a) (R : D → ι → polygonAlgebra a)
    (hV : ∀ d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (T d) j).val) (V d).val)
    (hR : ∀ d i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (T d) j).val) (R d i).val)
    (hcontrol : ∀ d i, SmallControlled B.c (B.gridPiece (by omega) Q h U W d i)
      (B.fullGeometricSector (by omega) (T d) (hT d) (V d)))
    (haction : ∀ d i (I : FiveAlphabet (Fin (m+1))) s j,
      ∀ x ∈ (B.gridPiece (by omega) Q h U W d j).range,
        B.gridInput (by omega) Q h U i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (B.gridInput (by omega) Q h U i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  apply supported_cell_patching (B.gridInput (by omega) Q h U) f hspec
    (fun d => ⨆ j, (B.gridPiece (by omega) Q h U W d j).range) ?_ ?_
    (fun d i => B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i))
    ?_ ?_ (by simp only [Fintype.card_fin]; omega)
  · rw [copyFamilyEval_range]
    exact B.gridPieces_generate (by omega) Q h U W hU hW hdisjoint hcover
  · exact B.gridInputs_normalize (by omega) Q h U W (by omega) none hU hW he
  · intro d I i s
    apply inner_action_iSup
    intro j
    exact haction d i I s j
  · intro d S hS w hw hrel
    have hh : (⨆ j, (B.gridPiece (by omega) Q h U W d j).range) ≤
        Subgroup.centralizer ({copyFamilyEval
          (fun i => B.fullGeometricSector (by omega) (T d) (hT d) (marginFamily (R d) (V d) i))
          (smallFamilyStarWord w)} : Set _) := by
      apply iSup_le
      intro j x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (B.actual_template_word_controls hlarge (T d) (hT d) (R d) (V d)
        (hR d) (hV d) _ (B.gridPiece_supported (by omega) Q h U W hU hW d j)
        (hcontrol d j) S hS w hw hrel x hx).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hh hx)).symm

end InitialCoverSystem
end GridFormalPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CrossingCellActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section LocalPatchTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι J : Type*}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

attribute [instance] LocalPatchTemplate.finite_index

namespace LocalPatchTemplate
variable {B} {F : Option ι → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {hlarge : 15 < m+1} (T : B.LocalPatchTemplate hlarge F f)

theorem masked_actions (h20 : 20 ≤ m+1)
    (hF : F none=B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
    (hf : ∀ j, B.AlignedSmallSupported (f j)) :
    ∀ i (I : FiveAlphabet (Fin (m+1))) s j, ∀ x ∈ (f j).range,
      F i (universalMap (subtypeAlternatingHom I.val) s)*x*
        (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  intro i I s j x hx
  let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
  cases i with
  | none =>
    have hh := B.cell_restrict_action h20 T.tests T.lawful (wholePolygon a) T.margin
      (fun _ _ _ => Iff.rfl) T.margin_resolved (f j) (hf j) (T.controlled j) I' s x hx
    rw [B.fullGeometricSector_whole,← hF] at hh
    have he : wholePolygon a ⊓ T.margin=T.margin := top_inf_eq _
    rw [he] at hh
    exact hh
  | some i =>
    exact (T.action i I s j x hx).trans (by
      simpa only [marginFamily,inf_comm] using B.cell_restrict_action h20 T.tests T.lawful
        (T.predicates i) T.margin (T.predicates_resolved i) T.margin_resolved
        (f j) (hf j) (T.controlled j) I' s x hx)

end LocalPatchTemplate

theorem grid_formal_patching_templates_oai {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    (hlarge : 25 ≤ m+1)
    (Q : (i : Option ι) → κ i → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (Q i))
    (U : Option ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector (by omega) (Q i) (h i) (W d)=
      B.fullGeometricSector (by omega) (Q none) (h none) (W d))
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (B.gridInput (by omega) Q h U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (hconst : U none=wholePolygon a)
    (hlocal : ∀ d, Nonempty (B.LocalPatchTemplate (by omega)
      (B.gridInput (by omega) Q h U) (B.gridPiece (by omega) Q h U W d))) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict := by
  classical
  let T := fun d => Classical.choice (hlocal d)
  apply B.grid_formal_patching hlarge Q h U W hU hW he hdisjoint hcover f hspec
    (fun d => (T d).tests) (fun d => (T d).lawful) (fun d => (T d).margin)
    (fun d => (T d).predicates) (fun d => (T d).margin_resolved)
    (fun d => (T d).predicates_resolved) (fun d => (T d).controlled)
  intro d
  apply (T d).masked_actions (by omega) ?_ (B.gridPiece_supported (by omega) Q h U W hU hW d)
  change B.fullGeometricSector _ (Q none) (h none) (U none)=_
  rw [hconst,B.fullGeometricSector_whole]

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_3, u_4, u_5} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates_oai.{u_3, u_4, u_5} := @OAI.SimpleAmenable.InitialCoverSystem.grid_formal_patching_templates_oai.{u_3, u_4, u_5}
