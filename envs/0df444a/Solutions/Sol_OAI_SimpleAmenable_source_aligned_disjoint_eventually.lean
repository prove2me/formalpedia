-- Prove2me | solution 1 for OAI.SimpleAmenable.source_aligned_disjoint_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:51:07.424392+00:00
-- url     : https://prove2.me/submissions/33143011-aa00-4940-abdf-5cd2ae29aa86

import Mathlib
import Definitions.Def_OAIQ65Sa008

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BoundedRelationCover
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
section BoundedRelationCover

variable (α : Type*) (L : ℕ)

variable {α} {G : Type*} [Group G] (f : α → G)

theorem mem_shortRelations_of_length [DecidableEq α] {L : ℕ} {w : FreeGroup α}
    (hw : FreeGroup.lift f w = 1) (hlen : w.toWord.length ≤ L) :
    w ∈ shortRelations L f := by
  classical
  refine ⟨⟨⟨⟨w.toWord.length,by omega⟩,fun i => w.toWord[i]⟩, ?_⟩,hw⟩
  change FreeGroup.mk (List.ofFn w.toWord.get) = w
  rw [List.ofFn_get]
  exact FreeGroup.mk_toWord

theorem finite_true_relations_bounded {R : Set (FreeGroup α)} (hR : R.Finite)
    (ht : ∀ w ∈ R, FreeGroup.lift f w = 1) :
    ∃ L : ℕ, R ⊆ shortRelations L f := by
  classical
  refine ⟨hR.toFinset.sup (fun w => w.toWord.length), ?_⟩
  intro w hw
  exact mem_shortRelations_of_length f (ht w hw)
    (Finset.le_sup (f := fun w => w.toWord.length) (hR.mem_toFinset.mpr hw))

end BoundedRelationCover

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FiniteCentralKernel
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
section FiniteCentralKernel

open scoped commutatorElement

variable {G H Q : Type*} [Group G] [Group H] [Group Q]

theorem subgroup_fg_of_comm {A : Type*} [CommGroup A] [Group.FG A] (K : Subgroup A) : K.FG := by
  let : Module.Finite ℤ (Additive A) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive A))
  apply (Subgroup.fg_iff_add_fg K).mpr
  exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule K.toAddSubgroup)).mp
    (IsNoetherian.noetherian _)

end FiniteCentralKernel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FinitelyManyTranslationRelations
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
section FinitelyManyTranslationRelations

open scoped IsMulCommutative

variable {β H : Type*} [Group H]

theorem freeAbelianHom_ext (φ ψ : Multiplicative (FreeAbelianGroup β) →* H)
    (h : ∀ i, φ (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
      ψ (Multiplicative.ofAdd (FreeAbelianGroup.of i))) : φ = ψ := by
  apply MonoidHom.ext
  intro x
  change φ (Multiplicative.ofAdd (Multiplicative.toAdd x)) = ψ (Multiplicative.ofAdd (Multiplicative.toAdd x))
  induction Multiplicative.toAdd x using FreeAbelianGroup.induction_on with
  | zero => exact (map_one φ).trans (map_one ψ).symm
  | of i => exact h i
  | neg x hx =>
      change φ ((Multiplicative.ofAdd (FreeAbelianGroup.of x))⁻¹) = ψ ((Multiplicative.ofAdd (FreeAbelianGroup.of x))⁻¹)
      rw [map_inv, map_inv, hx]
  | add x y hx hy =>
      change φ (Multiplicative.ofAdd x * Multiplicative.ofAdd y) = ψ (Multiplicative.ofAdd x * Multiplicative.ofAdd y)
      rw [map_mul, map_mul, hx, hy]

variable {α G : Type*} [Group G] (f : α → G)

theorem finite_word_equalities_eventually [Finite β] (u v : β → FreeGroup α)
    (huv : ∀ i, FreeGroup.lift f (u i) = FreeGroup.lift f (v i)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ i,
      PresentedGroup.mk (shortRelations M f) (u i) =
        PresentedGroup.mk (shortRelations M f) (v i) := by
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f
    (Set.finite_range (fun i => u i * (v i)⁻¹)) (by
      rintro w ⟨i,rfl⟩
      simp [huv])
  refine ⟨L,fun M hM i => ?_⟩
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (shortRelations_mono f hM (hL ⟨i,rfl⟩))

theorem commuting_words_lift_eventually [Finite β] (w : β → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j))) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.mk (shortRelations M f) (w i)) ∧
        (coverMap M f).comp t =
          commutingFamilyHom (fun i => FreeGroup.lift f (w i)) ht := by
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun p : β × β => w p.1 * w p.2) (fun p => w p.2 * w p.1)
    (fun p => by simpa only [map_mul] using (ht p.1 p.2).eq)
  refine ⟨L,fun M hM => ?_⟩
  let u : β → BoundedRelationCover M f := fun i => PresentedGroup.mk (shortRelations M f) (w i)
  have hu : ∀ i j, Commute (u i) (u j) := by
    intro i j
    have he := hL M hM (i,j)
    exact show u i * u j = u j * u i from by simpa only [map_mul] using he
  refine ⟨commutingFamilyHom u hu, fun i => commutingFamilyHom_of u hu i, ?_⟩
  apply freeAbelianHom_ext
  intro i
  simp [u]

end FinitelyManyTranslationRelations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectGeneratingFamilies
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

section FiniteTranslationCentralizers

variable {α β ι G : Type*} [Group G]

theorem translation_lattice_fg [Finite β] :
    Group.FG (Multiplicative (FreeAbelianGroup β)) :=
  Group.fg_of_surjective (translationWordMap_surjective (β := β))

theorem translation_centralizers_eventually [Finite β] [Finite ι]
    (f : α → G) (w : β → FreeGroup α) (v : ι → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j))) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∀ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
      (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.mk (shortRelations M f) (w i)) →
      ∀ i k, Commute (commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht k)
          (FreeGroup.lift f (v i)) →
        Commute (t k) (PresentedGroup.mk (shortRelations M f) (v i)) := by
  classical
  let T := Multiplicative (FreeAbelianGroup β)
  let : Group.FG T := translation_lattice_fg
  let q : T →* G := commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht
  let K (i : ι) : Subgroup T := (Subgroup.centralizer {FreeGroup.lift f (v i)}).comap q
  have hK (i : ι) : (K i).FG := subgroup_fg_of_comm (K i)
  choose S hS using hK
  let J := (i : ι) × ↥(S i)
  let z : J → T := fun j => j.2.val
  choose V hV using fun j : J => translationWordMap_surjective (z j)
  let W : FreeGroup β →* FreeGroup α := FreeGroup.lift w
  have he : (FreeGroup.lift f).comp W = q.comp (translationWordMap β) := by
    ext i
    simp only [MonoidHom.comp_apply,W,q,translationWordMap,FreeGroup.lift_apply_of]
    exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht i).symm
  have hc (j : J) : Commute (FreeGroup.lift f (W (V j))) (FreeGroup.lift f (v j.1)) := by
    have hz : z j ∈ K j.1 := by
      rw [← hS j.1]
      exact Subgroup.subset_closure j.2.property
    change q (z j) ∈ Subgroup.centralizer {_} at hz
    have hv : FreeGroup.lift f (W (V j)) = q (z j) := by
      simpa only [MonoidHom.comp_apply,hV j] using DFunLike.congr_fun he (V j)
    rw [hv]
    exact Subgroup.mem_centralizer_singleton_iff.mp hz
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun j : J => W (V j) * v j.1) (fun j => v j.1 * W (V j))
    (fun j => by simpa only [map_mul] using (hc j).eq)
  refine ⟨L,fun M hM t ht' i k hk => ?_⟩
  have he' : t.comp (translationWordMap β) =
      (PresentedGroup.mk (shortRelations M f)).comp W := by
    ext j
    simpa [translationWordMap,W] using ht' j
  have hk' : k ∈ K i := Subgroup.mem_centralizer_singleton_iff.mpr hk.eq
  have hle : K i ≤ (Subgroup.centralizer
      {PresentedGroup.mk (shortRelations M f) (v i)}).comap t := by
    rw [← hS i]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    let j : J := ⟨i,⟨x,hx⟩⟩
    have hv : t x = PresentedGroup.mk (shortRelations M f) (W (V j)) := by
      simpa only [MonoidHom.comp_apply,hV j] using DFunLike.congr_fun he' (V j)
    change t x ∈ Subgroup.centralizer {_}
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [hv]
    simpa only [map_mul] using hL M hM j
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk')

end FiniteTranslationCentralizers

section SourceCentralizingTranslations

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem source_centralizing_translation_lifts_eventually :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
          PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t =
          sourceLatticeMap a r m hm ∧
        ∀ s k, Commute (sourceLatticeMap a r m hm k)
            (alternatingGenerator a r m hm s) →
          Commute (t k) (PresentedGroup.of s) := by
  let f := alternatingGenerator a r m hm
  let w : Fin m × Fin 2 → FreeGroup (SourceGeneratorLabel m) :=
    fun i => FreeGroup.of (sourceTranslationLabel m i)
  have hc : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j)) := by
    intro i j
    exact source_translation_commute a r m hm i j
  obtain ⟨L₁,hL₁⟩ := commuting_words_lift_eventually f w hc
  obtain ⟨L₂,hL₂⟩ := translation_centralizers_eventually f w
    (fun s : SourceGeneratorLabel m => FreeGroup.of s) hc
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨t,ht,htq⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨t,ht,htq,?_⟩
  intro s k hk
  exact hL₂ M (le_trans (le_max_right _ _) hM) t ht s k hk

end SourceCentralizingTranslations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_ConditionalTranslationStabilizers
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section ConditionalTranslationStabilizers

variable {a m : ℕ}

theorem trackTranslation_conditional_commute (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → CutRing × CutRing)
    (hd : ∀ i, σ i ≠ i → d i = 0) :
    Commute (trackTranslation d) (conditionalHom U σ) := by
  have he := conditional_translation_conjugate U σ d 0 hd
  have hU : (⟨translate a (-0) ⁻¹' U.val,polygon_preimage_translate (-0) U.property⟩ :
      polygonAlgebra a) = U := by
    apply Subtype.ext
    ext p
    simp only [Set.mem_preimage,neg_zero,translate_zero]
  rw [hU] at he
  have hx := congrArg (fun z => z * trackTranslation d) he
  change _*_ = _*_
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hx.symm

theorem conditional_conjugation_support (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (d e : Fin m → CutRing × CutRing)
    (hde : ∀ i, σ i ≠ i → d i = e i) :
    trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ =
      trackTranslation e * conditionalHom U σ * (trackTranslation e)⁻¹ := by
  have hc := trackTranslation_conditional_commute U σ (d-e) (by
    intro i hi
    change d i - e i = 0
    rw [hde i hi,sub_self])
  rw [trackTranslation_sub] at hc
  have hcomm : Commute (trackTranslation (a := a) d) (trackTranslation e) := by
    change _*_ = _*_
    rw [← trackTranslation_add,← trackTranslation_add,add_comm d e]
  have he := congrArg (fun z => trackTranslation e * z * (trackTranslation d)⁻¹) hc.eq
  rw [hcomm.inv_right.eq] at he
  have hh : trackTranslation e * ((trackTranslation e)⁻¹ * trackTranslation d * conditionalHom U σ) *
      (trackTranslation d)⁻¹ = trackTranslation d * conditionalHom U σ * (trackTranslation d)⁻¹ := by group
  rw [hh] at he
  convert he using 1; group

end ConditionalTranslationStabilizers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_TranslatedDisjoint
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section TranslatedDisjoint

theorem generator_commutations_eventually {α G : Type*} [Finite α] [Group G]
    (f : α → G) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ i j, Commute (f i) (f j) →
      Commute (PresentedGroup.of i : BoundedRelationCover M f) (PresentedGroup.of j) := by
  let β := {p : α × α // Commute (f p.1) (f p.2)}
  obtain ⟨L,hL⟩ := finite_word_equalities_eventually f
    (fun p : β => FreeGroup.of p.val.1 * FreeGroup.of p.val.2)
    (fun p : β => FreeGroup.of p.val.2 * FreeGroup.of p.val.1)
    (fun p => by simpa only [map_mul,FreeGroup.lift_apply_of] using p.property.eq)
  refine ⟨L,fun M hM i j hij => ?_⟩
  have he := hL M hM ⟨(i,j),hij⟩
  change _*_ = _*_
  simpa only [map_mul,PresentedGroup.of] using he

theorem lifted_common_shift_commute {A G H : Type*} [CommGroup A] [Group G] [Group H]
    (q : A →* G) (t : A →* H) (x₁ x₂ : G) (y₁ y₂ : H)
    (hc₁ : ∀ k, Commute (q k) x₁ → Commute (t k) y₁)
    (hc₂ : ∀ k, Commute (q k) x₂ → Commute (t k) y₂)
    (hy : Commute y₁ y₂) (u v w : A)
    (hw₁ : q u*x₁*(q u)⁻¹ = q w*x₁*(q w)⁻¹)
    (hw₂ : q v*x₂*(q v)⁻¹ = q w*x₂*(q w)⁻¹) :
    Commute (t u*y₁*(t u)⁻¹) (t v*y₂*(t v)⁻¹) := by
  rw [lifted_translation_orbit_independent q t x₁ y₁ hc₁ u w hw₁,
    lifted_translation_orbit_independent q t x₂ y₂ hc₂ v w hw₂]
  change _*_ = _*_
  calc
    _ = t w*(y₁*y₂)*(t w)⁻¹ := by group
    _ = t w*(y₂*y₁)*(t w)⁻¹ := by rw [hy.eq]
    _ = _ := by group

theorem conditionalHom_disjoint_alphabets {a m : ℕ} (U V : polygonAlgebra a)
    (σ ρ : Equiv.Perm (Fin m)) (h : Disjoint σ.support ρ.support) :
    Commute (conditionalHom U σ) (conditionalHom V ρ) := by
  have hh := Equiv.Perm.Disjoint.commute (Equiv.Perm.disjoint_iff_disjoint_support.mpr h)
  change _*_ = _*_
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm U σ (conditionalPerm V ρ p) =
    conditionalPerm V ρ (conditionalPerm U σ p)
  have hp := DFunLike.congr_fun hh.eq p.1
  simp only [Equiv.Perm.mul_apply] at hp
  by_cases hu : p.2 ∈ U.val <;> by_cases hv : p.2 ∈ V.val
  all_goals simp [conditionalPerm,hu,hv,hp]

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem source_disjoint_common_shift
    (σ ρ : Equiv.Perm (Fin (m+1))) (hd : Disjoint σ.support ρ.support)
    (hb : σ.support.card + ρ.support.card < m+1)
    (U V : polygonAlgebra a)
    (u v : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    ∃ w, sourceLatticeFullMap a r m hm u * conditionalHom U σ *
        (sourceLatticeFullMap a r m hm u)⁻¹ =
      sourceLatticeFullMap a r m hm w * conditionalHom U σ *
        (sourceLatticeFullMap a r m hm w)⁻¹ ∧
      sourceLatticeFullMap a r m hm v * conditionalHom V ρ *
        (sourceLatticeFullMap a r m hm v)⁻¹ =
      sourceLatticeFullMap a r m hm w * conditionalHom V ρ *
        (sourceLatticeFullMap a r m hm w)⁻¹ := by
  classical
  obtain ⟨d,hu⟩ := sourceLatticeFullMap_translation a r m hm u
  obtain ⟨e,hv⟩ := sourceLatticeFullMap_translation a r m hm v
  have hcard : (σ.support ∪ ρ.support).card < (Finset.univ : Finset (Fin (m+1))).card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      lt_of_le_of_lt (Finset.card_union_le _ _) hb
  obtain ⟨b,_,hbi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  let z : Fin (m+1) → CutRing × CutRing := fun i => if i ∈ σ.support then d i else e i
  obtain ⟨w,f,hw,hf⟩ := sourceLatticeFullMap_prescribed a r m hm
    (σ.support ∪ ρ.support) b hbi z
  refine ⟨w,?_,?_⟩
  · rw [hu,hw]
    apply conditional_conjugation_support
    intro i hi
    have hi' : i ∈ σ.support := Equiv.Perm.mem_support.mpr hi
    rw [hf i (Finset.mem_union_left _ hi')]
    simp only [z,ite_eq_left hi']
  · rw [hv,hw]
    apply conditional_conjugation_support
    intro i hi
    have hi' : i ∈ ρ.support := Equiv.Perm.mem_support.mpr hi
    have hin : i ∉ σ.support := fun h => Finset.disjoint_left.mp hd h hi'
    rw [hf i (Finset.mem_union_right _ hi')]
    simp only [z,ite_eq_right hin]

theorem source_translated_disjoint_eventually (hm' : 10 < m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
        ∀ (j k : Fin 5)
          (σ ρ : {σ : Equiv.Perm (Fin (m+1)) //
            σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}),
            Disjoint σ.val.support ρ.val.support → ∀ u v,
            Commute (t u * PresentedGroup.of (Sum.inl (j,σ)) * (t u)⁻¹)
              (t v * PresentedGroup.of (Sum.inl (k,ρ)) * (t v)⁻¹) := by
  obtain ⟨L₁,hL₁⟩ := source_centralizing_translation_lifts_eventually a r m hm
  obtain ⟨L₂,hL₂⟩ := generator_commutations_eventually (alternatingGenerator a r m hm)
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨t,ht,htq,hc⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨t,ht,htq,?_⟩
  intro j k σ ρ hd u v
  have hy : Commute (PresentedGroup.of (Sum.inl (j,σ)) :
      BoundedRelationCover M (alternatingGenerator a r m hm))
      (PresentedGroup.of (Sum.inl (k,ρ))) := by
    apply hL₂ M (le_trans (le_max_right _ _) hM)
    change _*_ = _*_
    apply Subtype.ext
    exact (conditionalHom_disjoint_alphabets (initialTest a r j)
      (initialTest a r k) σ.val ρ.val hd).eq
  obtain ⟨w,hw₁,hw₂⟩ := source_disjoint_common_shift a r m hm σ.val ρ.val hd
    (by have hσ := σ.property.2; have hρ := ρ.property.2; omega)
    (initialTest a r j) (initialTest a r k) u v
  apply lifted_common_shift_commute (sourceLatticeMap a r m hm) t
    (alternatingGenerator a r m hm (Sum.inl (j,σ)))
    (alternatingGenerator a r m hm (Sum.inl (k,ρ))) _ _
    (hc (Sum.inl (j,σ))) (hc (Sum.inl (k,ρ))) hy u v w
  · apply Subtype.ext
    exact hw₁
  · apply Subtype.ext
    exact hw₂

end TranslatedDisjoint

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AlignedGroups
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section AlignedGroups

variable {A H : Type*} [Group A] [Group H] {B : Type*}

theorem alignedGroup_commute (t : A →* H) (x : B → H) (P Q : B → Prop)
    (hc : ∀ b, P b → ∀ c, Q c → ∀ u v,
      Commute (t u*x b*(t u)⁻¹) (t v*x c*(t v)⁻¹)) :
    ∀ g ∈ alignedGroup t x P, ∀ h ∈ alignedGroup t x Q, Commute g h := by
  have hh : alignedGroup t x P ≤ Subgroup.centralizer (alignedGroup t x Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨b,hb,u,rfl⟩
    rw [alignedGroup,Subgroup.centralizer_closure]
    intro h hh
    obtain ⟨c,hc',v,rfl⟩ := hh
    exact (hc b hb c hc' u v).symm.eq
  intro g hg h hmem
  exact (hh hg h hmem).symm

end AlignedGroups

section SourceAlignedGroups

theorem source_aligned_disjoint_eventually_oai (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hm' : 10 < m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = PresentedGroup.of (Sum.inr i)) ∧
        (coverMap M (alternatingGenerator a r m hm)).comp t = sourceLatticeMap a r m hm ∧
        ∀ (I J : Finset (Fin (m+1))), Disjoint I J →
          ∀ g ∈ sourceAlignedGroup a r m hm M t I,
          ∀ h ∈ sourceAlignedGroup a r m hm M t J, Commute g h := by
  obtain ⟨L,hL⟩ := source_translated_disjoint_eventually a r m hm hm'
  refine ⟨L,fun M hM => ?_⟩
  obtain ⟨t,ht,htq,hc⟩ := hL M hM
  refine ⟨t,ht,htq,?_⟩
  intro I J hIJ
  apply alignedGroup_commute
  intro b hb c hc' u v
  exact hc b.1 c.1 b.2 c.2 (hIJ.mono hb hc') u v

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.source_aligned_disjoint_eventually_oai := @OAI.SimpleAmenable.source_aligned_disjoint_eventually_oai
