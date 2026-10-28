-- Prove2me | solution 1 for OAI.SimpleAmenable.initialCoverSystem_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:55:55.729636+00:00
-- url     : https://prove2.me/submissions/8833d5ee-a4f3-421c-878d-83af38089f26

import Mathlib
import Definitions.Def_OAIQ65Sa011
import Theorems.Thm_OAI_SimpleAmenable_source_aligned_disjoint_eventually

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

theorem finite_table_lift {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (w : T → FreeGroup α) (hw : ∀ t, FreeGroup.lift f (w t) = φ t) :
    ∃ (L : ℕ) (ρ : T →* BoundedRelationCover L f),
      (coverMap L f).comp ρ = φ ∧
      ∀ t, ρ t = PresentedGroup.mk (shortRelations L f) (w t) := by
  classical
  let R : Set (FreeGroup α) := {w 1} ∪
    Set.range (fun p : T × T => w p.1 * w p.2 * (w (p.1*p.2))⁻¹)
  have hRf : R.Finite := (Set.finite_singleton _).union (Set.finite_range _)
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f hRf (by
    intro z hz
    rcases hz with hz | ⟨⟨s,t⟩,rfl⟩
    · rcases hz with rfl
      simp [hw]
    · simp [hw])
  let ρ : T →* BoundedRelationCover L f :=
    { toFun := fun t => PresentedGroup.mk (shortRelations L f) (w t)
      map_one' := PresentedGroup.one_of_mem (hL (Set.mem_union_left _ (Set.mem_singleton _)))
      map_mul' := by
        intro s t
        have he := PresentedGroup.one_of_mem (hL (Set.mem_union_right _
          (Set.mem_range.mpr ⟨(s,t),rfl⟩)))
        simp only [map_mul, map_inv, mul_inv_eq_one] at he
        exact he.symm }
  refine ⟨L,ρ,?_,fun _ => rfl⟩
  ext t
  exact hw t

end BoundedRelationCover

section CoherentBoundedCovers
variable {α G : Type*} [Group G] (f : α → G)

theorem coverTransition_projection {L M : ℕ} (hLM : L ≤ M) :
    (coverMap M f).comp (coverTransition f hLM) = coverMap L f := by
  ext a
  simp only [MonoidHom.comp_apply, PresentedGroup.of, coverTransition_mk, coverMap_mk]

theorem finite_table_lift_eventually {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (w : T → FreeGroup α) (hw : ∀ t, FreeGroup.lift f (w t) = φ t) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∃ ρ : T →* BoundedRelationCover M f,
      (coverMap M f).comp ρ = φ ∧
      ∀ t, ρ t = PresentedGroup.mk (shortRelations M f) (w t) := by
  obtain ⟨L,ρ,hρ,hword⟩ := finite_table_lift f φ w hw
  refine ⟨L,fun M hM => ⟨(coverTransition f hM).comp ρ,?_,?_⟩⟩
  · rw [← MonoidHom.comp_assoc,coverTransition_projection,hρ]
  · intro t
    simp only [MonoidHom.comp_apply,hword,coverTransition_mk]

theorem bounded_cover_eventually_perfect [Finite α] [Group.IsPerfect G]
    (hf : Function.Surjective (FreeGroup.lift f)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Group.IsPerfect (BoundedRelationCover M f) := by
  classical
  have hmap : (commutator (FreeGroup α)).map (FreeGroup.lift f) = ⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,
      ← commutator_def,Group.IsPerfect.commutator_eq_top]
  have hex (a : α) : ∃ w ∈ commutator (FreeGroup α), FreeGroup.lift f w = f a :=
    Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top (f a))
  choose w hw hwe using hex
  let R : Set (FreeGroup α) := Set.range (fun a => w a * (FreeGroup.of a)⁻¹)
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f (R := R) (Set.finite_range _) (by
    rintro r ⟨a,rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hwe, mul_inv_cancel])
  refine ⟨L,fun M hM => ?_⟩
  let π := PresentedGroup.mk (shortRelations M f)
  have hgen (a : α) : π (FreeGroup.of a) ∈ commutator (BoundedRelationCover M f) := by
    have he : π (w a) = π (FreeGroup.of a) :=
      PresentedGroup.mk_eq_mk_of_mul_inv_mem
        (shortRelations_mono f hM (hL (Set.mem_range.mpr ⟨a,rfl⟩)))
    rw [← he]
    have hle : (commutator (FreeGroup α)).map π ≤ commutator (BoundedRelationCover M f) := by
      rw [map_commutator_eq,commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hle (Subgroup.mem_map.mpr ⟨w a,hw a,rfl⟩)
  constructor
  apply top_unique
  intro g hg
  clear hg
  obtain ⟨z,rfl⟩ := PresentedGroup.mk_surjective (shortRelations M f) g
  induction z using OAI.freeGroupInductionOn with
  | one => exact (commutator _).one_mem
  | of a => exact hgen a
  | inv_of a ha => exact (commutator _).inv_mem ha
  | mul x y hx hy => exact (commutator _).mul_mem hx hy

end CoherentBoundedCovers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalBooleanGeneration
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
section ConditionalBooleanGeneration

open scoped commutatorElement

theorem sourceGenerated_le_alternating (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) :
    sourceGenerated a r m ≤ polygonAlternatingGroup a (m+1) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s,rfl⟩
  exact sourceGenerator_mem a r m hm s

theorem balanced_translation_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (i : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single i v - Pi.single (Fin.last m) v) ∈ sourceGenerated a r m := by
  classical
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  let dx : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (cutTau,0) - Pi.single (Fin.last m) (cutTau,0)
  let dy : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc (0,cutTau) - Pi.single (Fin.last m) (0,cutTau)
  have hx : trackTranslation (a := a) dx ∈ sourceGenerated a r m :=
    sourceGenerator_mem_generated a r m (Sum.inr (i,0))
  have hy : trackTranslation (a := a) dy ∈ sourceGenerated a r m := by
    simpa only [sourceGenerator,show (1 : Fin 2) ≠ 0 by decide,ite_false]
      using sourceGenerator_mem_generated a r m (Sum.inr (i,1))
  have he : trackTranslation (a := a) (Pi.single i.castSucc v - Pi.single (Fin.last m) v) =
      trackTranslation (v.1.im • dx + v.2.im • dy) := by
    let d : Fin (m+1) → CutRing × CutRing := Pi.single i.castSucc v - Pi.single (Fin.last m) v
    change trackTranslation d = _
    rw [trackTranslation_reduce d]
    congr 1
    funext k
    by_cases hki : k = i.castSucc <;> by_cases hkl : k = Fin.last m <;>
      apply Prod.ext <;> simp [d,dx,dy,hki,hkl,zsmul_eq_mul]
  rw [he,trackTranslation_add,trackTranslation_zsmul,trackTranslation_zsmul]
  exact (sourceGenerated a r m).mul_mem ((sourceGenerated a r m).zpow_mem hx _)
    ((sourceGenerated a r m).zpow_mem hy _)

theorem balanced_difference_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (i j : Fin (m+1)) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈ sourceGenerated a r m := by
  have he : (Pi.single j v - Pi.single i v : Fin (m+1) → CutRing × CutRing) =
      (Pi.single j v - Pi.single (Fin.last m) v) -
        (Pi.single i v - Pi.single (Fin.last m) v) := by abel
  rw [he,trackTranslation_sub]
  exact (sourceGenerated a r m).mul_mem (balanced_translation_generated a r m j v)
    ((sourceGenerated a r m).inv_mem (balanced_translation_generated a r m i v))

end ConditionalBooleanGeneration

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

theorem finite_table_with_inputs_eventually {T : Type*} [Group T] [Finite T]
    [Finite β] (φ : T →* G) (input : β → T) (w : β → FreeGroup α)
    (hw : ∀ i, FreeGroup.lift f (w i) = φ (input i))
    (hf : Function.Surjective (FreeGroup.lift f)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∃ ρ : T →* BoundedRelationCover M f,
      (coverMap M f).comp ρ = φ ∧
      ∀ i, ρ (input i) = PresentedGroup.mk (shortRelations M f) (w i) := by
  choose W hW using fun t : T => hf (φ t)
  obtain ⟨L₁,hL₁⟩ := finite_table_lift_eventually f φ W hW
  obtain ⟨L₂,hL₂⟩ := finite_word_equalities_eventually f (fun i => W (input i)) w
    (fun i => (hW (input i)).trans (hw i).symm)
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hρW⟩ := hL₁ M (le_trans (le_max_left _ _) hM)
  refine ⟨ρ,hρ,fun i => ?_⟩
  rw [hρW, hL₂ M (le_trans (le_max_right _ _) hM)]

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
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
section LocalDisplacement

theorem fresh_nine_tracks {m : ℕ} (hm : 15 ≤ m) (s t : Fin 3 → Fin m) :
    ∃ e : Fin 9 ↪ Fin m, ∀ i j, e i ≠ s j ∧ e i ≠ t j := by
  classical
  let used := Finset.univ.image s ∪ Finset.univ.image t
  have hu : used.card ≤ 6 := by
    apply (Finset.card_union_le _ _).trans
    change _ + _ ≤ 3 + 3
    apply add_le_add <;> exact Finset.card_image_le.trans (by simp)
  have hc : 9 ≤ usedᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have he : Nonempty (Fin 9 ↪ {x : Fin m // x ∈ usedᶜ}) := by
    rw [Function.Embedding.nonempty_iff_card_le,Fintype.card_fin,Fintype.card_coe]
    exact hc
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Function.Embedding.subtype _),?_⟩
  intro i j
  have hn : (e i).val ∉ used := Finset.mem_compl.mp (e i).property
  constructor <;> intro heq <;> apply hn
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiveTrackGeneration
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
section FiveTrackGeneration

theorem alphabetTranslation_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (u : CutRing × CutRing) :
    trackTranslation (a := a) (alphabetTranslation ι b u) ∈ sourceGenerated a r m := by
  classical
  unfold alphabetTranslation
  induction (Finset.univ : Finset (Fin 5)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,trackTranslation_add]
    exact (sourceGenerated a r m).mul_mem (balanced_difference_generated a r m b (ι i) u) ih

theorem alphabetTranslation_apply {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (b : Fin m) (hb : b ∉ Set.range ι) (u : CutRing × CutRing) (j : Fin 5) :
    alphabetTranslation ι b u (ι j) = u := by
  classical
  have hb' : ∀ k, ι k ≠ b := fun k h => hb ⟨k,h⟩
  simp [alphabetTranslation,Finset.sum_apply,Pi.single_apply,ι.injective.eq_iff,hb']

theorem fiveTrack_translate_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a)
    (hU : ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) U)
    (u : CutRing × CutRing) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m)
      ⟨translate a u ⁻¹' U.val,polygon_preimage_translate u U.property⟩ := by
  intro g
  let d := alphabetTranslation ι b (-u)
  have hd : ∀ i, fiveTrackHom ι g i ≠ i → d i = -u := by
    intro i hi
    have hi' : i ∈ Set.range ι := by
      by_contra hn
      exact hi (Equiv.Perm.viaEmbedding_apply_of_notMem g.val ι i hn)
    obtain ⟨j,rfl⟩ := hi'
    exact alphabetTranslation_apply ι b hb (-u) j
  have he := conditional_translation_conjugate U (fiveTrackHom ι g) d (-u) hd
  simp only [neg_neg] at he
  rw [he]
  have ht := alphabetTranslation_generated a r m ι b (-u)
  exact (sourceGenerated a r m).mul_mem ((sourceGenerated a r m).mul_mem ht (hU g))
    ((sourceGenerated a r m).inv_mem ht)

theorem fiveTrackBoolean_translate (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (u : CutRing × CutRing) {U : Set (GenericSquare a)}
    (hU : U ∈ fiveTrackBoolean a r m ι) :
    translate a u ⁻¹' U ∈ fiveTrackBoolean a r m ι := by
  obtain ⟨hU,hU'⟩ := hU
  exact ⟨polygon_preimage_translate u hU,
    fiveTrack_translate_generated a r m ι b hb ⟨U,hU⟩ hU' u⟩

theorem fiveTrackBoolean_initial (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    (initialTest a r j).val ∈ fiveTrackBoolean a r m ι :=
  ⟨(initialTest a r j).property,fiveTrack_initial_generated a r m ι j⟩

theorem fiveTrackBoolean_coordinate (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (j : Fin 2) (z : CutRing) :
    halfPlane a (Fin.castLE (by omega) j) z ∈ fiveTrackBoolean a r m ι := by
  apply coordinate_cuts_generated _ j
    (fun u _ hU => fiveTrackBoolean_translate a r m ι b hb u hU)
  fin_cases j
  · exact fiveTrackBoolean_initial a r m ι 1
  · exact fiveTrackBoolean_initial a r m ι 2

end FiveTrackGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShiftedSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem slotHom_supported {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (σ : Equiv.Perm (Fin n)) :
    SupportedIn (slotHom U s hs σ).val (Set.range (SlotMap a m U s)) := by
  intro p hp
  exact slotPerm_apply_of_notMem U s hs σ hp

theorem slotHom_subcycle {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (ι : Fin 3 ↪ Fin n) :
    slotHom U s hs (trackCycle ι) =
      slotHom U (s ∘ ι) (subslots_injective U s hs ι) (trackCycle (Function.Embedding.refl _)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U (s ∘ ι))
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change slotPerm U s hs _ (SlotMap a m U s (ι i,x)) =
      slotPerm U (s ∘ ι) _ _ (SlotMap a m U (s ∘ ι) (i,x))
    rw [slotPerm_apply,slotPerm_apply,trackCycle_apply]
    have hi : trackCycle (Function.Embedding.refl (Fin 3)) i = i+1 :=
      trackCycle_apply (Function.Embedding.refl _) i
    rw [hi]
    rfl
  · rw [slotHom_supported U (s ∘ ι) _ _ p hp]
    by_cases hP : p ∈ Set.range (SlotMap a m U s)
    · obtain ⟨⟨j,x⟩,rfl⟩ := hP
      change slotPerm U s hs _ _ = _
      rw [slotPerm_apply]
      have hj : j ∉ Set.range ι := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),rfl⟩
      rw [trackCycle_apply_of_notMem ι hj]
    · exact slotHom_supported U s hs _ p hP

theorem threeSlot_eq_slotHom {a m : ℕ} {g : polygonFullGroup a m}
    (hg : IsThreeSlotCycle g) :
    ∃ (U : polygonAlgebra a) (s : Fin 3 → Fin m × (CutRing × CutRing))
      (hs : Function.Injective (SlotMap a m U s)),
      g = slotHom U s hs (trackCycle (Function.Embedding.refl _)) := by
  obtain ⟨U,s,hU,hs,hact,hfix⟩ := hg
  refine ⟨U,s,hs,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U s)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change g.val (SlotMap a m U s (i,x)) = slotPerm U s hs _ _
    rw [hact,slotPerm_apply]
    exact (congrArg (fun j => SlotMap a m U s (j,x))
      (trackCycle_apply (Function.Embedding.refl (Fin 3)) i)).symm
  · exact (hfix p hp).trans (slotPerm_apply_of_notMem U s hs _ hp).symm

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GenuineFiniteGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section GenuineFiniteGeneration

theorem fiveTrackBoolean_polygon (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : U.val ∈ fiveTrackBoolean a r m ι := by
  let B := fiveTrackBoolean a r m ι
  have hcoord := fiveTrackBoolean_coordinate a r m ι b hb
  have htrans := fun u U hU => fiveTrackBoolean_translate a r m ι b hb u (U := U) hU
  apply polygon_induction (P := fun U => U ∈ B) ?_ BooleanSubalgebra.bot_mem
    (fun _ _ hU hV => BooleanSubalgebra.sup_mem hU hV)
    (fun _ hU => BooleanSubalgebra.compl_mem hU) U.property
  intro j z
  fin_cases j
  · exact hcoord 0 z
  · exact hcoord 1 z
  · exact slope_cuts_generated r hr B htrans hcoord 2 (Or.inl rfl)
      (fiveTrackBoolean_initial a r m ι 3) z
  · exact slope_cuts_generated r hr B htrans hcoord 3 (Or.inr rfl)
      (fiveTrackBoolean_initial a r m ι 4) z

theorem fiveTrack_polygon_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (ι : Fin 5 ↪ Fin (m+1)) (b : Fin (m+1)) (hb : b ∉ Set.range ι)
    (U : polygonAlgebra a) : ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) U := by
  obtain ⟨_,h⟩ := fiveTrackBoolean_polygon a r m hr ι b hb U
  exact h

private theorem extend_three_tracks {m : ℕ} (hm : 15 ≤ m) (s : Fin 3 ↪ Fin m) :
    ∃ (ι : Fin 5 ↪ Fin m) (b : Fin m), (∀ i, ι (threeInFive i) = s i) ∧ b ∉ Set.range ι := by
  obtain ⟨e,he⟩ := fresh_nine_tracks hm s s
  let t : Fin 5 → Fin m := ![s 0,s 1,s 2,e 0,e 1]
  have hs : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals dsimp only [t,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four] at hij
    all_goals first | rfl | exact False.elim (by have := s.injective hij; contradiction) |
      exact False.elim (by have := e.injective hij; contradiction) |
      exact False.elim ((he _ _).1 hij) | exact False.elim ((he _ _).1 hij.symm)
  refine ⟨⟨t,hs⟩,e 2,?_,?_⟩
  · intro i
    fin_cases i <;> rfl
  · rintro ⟨i,hi⟩
    fin_cases i
    all_goals dsimp only [Function.Embedding.coeFn_mk,t,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at hi
    all_goals first | exact (he _ _).1 hi.symm |
      exact False.elim (by have := e.injective hi; contradiction)

theorem trackCycle_viaEmbedding {m n : ℕ} (ι : Fin m ↪ Fin n) (s : Fin 3 ↪ Fin m) :
    (trackCycle s).viaEmbedding ι = trackCycle (s.trans ι) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨y,rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply]
    by_cases hy : y ∈ Set.range s
    · obtain ⟨i,rfl⟩ := hy
      rw [trackCycle_apply]
      exact (trackCycle_apply (s.trans ι) i).symm
    · rw [trackCycle_apply_of_notMem s hy,trackCycle_apply_of_notMem (s.trans ι)]
      rintro ⟨i,hi⟩
      exact hy ⟨i,ι.injective hi⟩
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx,trackCycle_apply_of_notMem]
    rintro ⟨i,hi⟩
    exact hx ⟨s i,hi⟩

theorem conditional_cycle_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (U : polygonAlgebra a) (s : Fin 3 ↪ Fin (m+1)) :
    conditionalHom U (trackCycle s) ∈ sourceGenerated a r m := by
  obtain ⟨ι,b,he,hb⟩ := extend_three_tracks hm s
  have hg : trackCycle threeInFive ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have h := fiveTrack_polygon_generated a r m hr ι b hb U ⟨trackCycle threeInFive,hg⟩
  change conditionalHom U ((trackCycle threeInFive).viaEmbedding ι) ∈ _ at h
  rw [trackCycle_viaEmbedding] at h
  have hs : threeInFive.trans ι = s := Function.Embedding.ext he
  simpa only [hs] using h

theorem offsetFrame_apply {m n : ℕ} (s : Fin n ↪ Fin m) (b : Fin m)
    (hb : b ∉ Set.range s) (u : Fin n → CutRing × CutRing) (i : Fin n) :
    offsetFrame s b u (s i) = u i := by
  classical
  have hbi : s i ≠ b := fun h => hb ⟨i,h⟩
  simp only [offsetFrame,Finset.sum_apply,Pi.sub_apply,Pi.single_apply, hbi,ite_false,sub_zero]
  have he : (∑ j : Fin n, if s i = s j then u j else 0) = u i := by
    simp only [s.injective.eq_iff]
    simp
  exact he

theorem offsetFrame_generated (a : ℕ) (r : CutRing) (m n : ℕ)
    (s : Fin n ↪ Fin (m+1)) (b : Fin (m+1)) (u : Fin n → CutRing × CutRing) :
    trackTranslation (a := a) (offsetFrame s b u) ∈ sourceGenerated a r m := by
  classical
  unfold offsetFrame
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [trackTranslation_zero]
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi,trackTranslation_add]
      exact (sourceGenerated a r m).mul_mem (balanced_difference_generated a r m b (s i) (u i)) ih

theorem distinct_track_cycle_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (U : polygonAlgebra a) (s : Fin 3 → Fin (m+1) × (CutRing × CutRing))
    (ht : Function.Injective (fun i => (s i).1))
    (hs : Function.Injective (SlotMap a (m+1) U s)) :
    slotHom U s hs (trackCycle (Function.Embedding.refl _)) ∈ sourceGenerated a r m := by
  classical
  let ι : Fin 3 ↪ Fin (m+1) := ⟨fun i => (s i).1,ht⟩
  obtain ⟨b,c,_,hb,_⟩ := two_spare_tracks (by omega : 5 ≤ m+1) ι
  have hb' : b ∉ Set.range ι := by rintro ⟨i,hi⟩; exact hb i hi
  let d := offsetFrame ι b (fun i => (s i).2)
  have hd := offsetFrame_generated a r m 3 ι b (fun i => (s i).2)
  have heq : trackTranslation (a := a) d * conditionalHom U (trackCycle ι) *
      (trackTranslation d)⁻¹ = slotHom U s hs (trackCycle (Function.Embedding.refl _)) := by
    have he (i : Fin 3) (x : U.val) :
        (trackTranslation (a := a) d).val (ι i,x.val) = SlotMap a (m+1) U s (i,x) := by
      change (ι i,translate a (d (ι i)) x.val) = _
      dsimp only [d]
      rw [offsetFrame_apply ι b hb']
      rfl
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨p,rfl⟩ := (trackTranslation (a := a) d).val.surjective y
    change (trackTranslation (a := a) d).val
      (conditionalPerm U (trackCycle ι) ((trackTranslation d).val.symm ((trackTranslation d).val p))) = _
    rw [Equiv.symm_apply_apply]
    by_cases hx : p.2 ∈ U.val
    · by_cases hi : p.1 ∈ Set.range ι
      · obtain ⟨i,hi⟩ := hi
        obtain ⟨j,x⟩ := p
        dsimp at hx hi
        subst j
        change (trackTranslation (a := a) d).val
          (if x ∈ U.val then trackCycle ι (ι i) else ι i,x) = _
        simp only [hx,ite_true,trackCycle_apply]
        rw [he (i+1) ⟨x,hx⟩,he i ⟨x,hx⟩]
        change _ = slotPerm U s hs _ _
        rw [slotPerm_apply]
        have hz := trackCycle_apply (Function.Embedding.refl (Fin 3)) i
        change trackCycle (Function.Embedding.refl (Fin 3)) i = i+1 at hz
        rw [hz]
      · have hf : conditionalPerm U (trackCycle ι) p = p := by
          simp [conditionalPerm,trackCycle_apply_of_notMem ι hi]
        rw [hf]
        symm
        apply slotPerm_apply_of_notMem
        rintro ⟨⟨i,x⟩,hi'⟩
        rw [← he] at hi'
        have hh := (trackTranslation (a := a) d).val.injective hi'
        exact hi ⟨i,congrArg Prod.fst hh⟩
    · have hf : conditionalPerm U (trackCycle ι) p = p := by
        change (if p.2 ∈ U.val then trackCycle ι p.1 else p.1,p.2) = p
        simp only [hx,ite_false]
      rw [hf]
      symm
      apply slotPerm_apply_of_notMem
      rintro ⟨⟨i,x⟩,hi'⟩
      rw [← he] at hi'
      have hh := (trackTranslation (a := a) d).val.injective hi'
      exact hx (congrArg Prod.snd hh ▸ x.property)
  rw [← heq]
  exact (sourceGenerated a r m).mul_mem
    ((sourceGenerated a r m).mul_mem hd (conditional_cycle_generated a r m hr hm U ι))
    ((sourceGenerated a r m).inv_mem hd)

private theorem star_cycle_identity :
    trackCycle (starThreeInFive 0) * trackCycle (starThreeInFive 1) *
      trackCycle (starThreeInFive 2) * trackCycle (starThreeInFive 0) *
      trackCycle (starThreeInFive 1) = trackCycle threeInFive := by decide

theorem threeSlot_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (g : polygonFullGroup a (m+1)) (hg : IsThreeSlotCycle g) :
    g ∈ sourceGenerated a r m := by
  obtain ⟨U,s,hs,rfl⟩ := threeSlot_eq_slotHom hg
  obtain ⟨k,l,hkl,hk,hl⟩ := two_spare_tracks (by omega : 5 ≤ m+1) (fun i => (s i).1)
  let S := extendSlots s k l
  have hS := extendSlots_injective U s hs k l hkl hk hl
  let φ := slotHom U S hS
  have hi (i : Fin 3) : φ (trackCycle (starThreeInFive i)) ∈ sourceGenerated a r m := by
    rw [slotHom_subcycle]
    apply distinct_track_cycle_generated a r m hr hm
    intro j n he
    fin_cases i <;> fin_cases j <;> fin_cases n
    all_goals dsimp [S,starThreeInFive,extendSlots,threeInFive] at he
    all_goals first | rfl | exact False.elim (hkl he) | exact False.elim (hkl he.symm) |
      exact False.elim (hk _ he) | exact False.elim (hl _ he) |
      exact False.elim (hk _ he.symm) | exact False.elim (hl _ he.symm)
  have h := (sourceGenerated a r m).mul_mem
    ((sourceGenerated a r m).mul_mem ((sourceGenerated a r m).mul_mem
      ((sourceGenerated a r m).mul_mem (hi 0) (hi 1)) (hi 2)) (hi 0)) (hi 1)
  simp only [← map_mul,star_cycle_identity] at h
  rw [slotHom_subcycle] at h
  have he : S ∘ threeInFive = s := funext (extendSlots_three s k l)
  simpa only [he] using h

theorem sourceGenerated_eq_alternating (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) :
    sourceGenerated a r m = polygonAlternatingGroup a (m+1) := by
  apply le_antisymm (sourceGenerated_le_alternating a r m (by omega))
  apply (Subgroup.closure_le _).mpr
  exact threeSlot_generated a r m hr hm

theorem alternatingGenerator_surjective (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1)
    (hm' : 2 ≤ m) : Function.Surjective (FreeGroup.lift (alternatingGenerator a r m hm')) := by
  rw [FreeGroup.lift_surjective_iff_closure_range_eq_top]
  apply Subgroup.map_injective (polygonAlternatingGroup a (m+1)).subtype_injective
  rw [← MonoidHom.range_eq_map,Subgroup.range_subtype,MonoidHom.map_closure]
  have he : (polygonAlternatingGroup a (m+1)).subtype ''
      Set.range (alternatingGenerator a r m hm') = Set.range (sourceGenerator a r m) := by
    rw [← Set.range_comp]
    rfl
  rw [he]
  exact sourceGenerated_eq_alternating a r m hr hm

theorem sourceCover_eventually_perfect (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) (hm' : 2 ≤ m) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm')) := by
  let := polygonAlternatingGroup_perfect a (m+1) (by omega)
  exact bounded_cover_eventually_perfect _ (alternatingGenerator_surjective a r m hr hm hm')

end GenuineFiniteGeneration

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InitialPointwiseTable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SourceInitialPointwiseTable

variable {a m : ℕ} {ι : Type*} [Finite ι]

theorem source_initial_table_lifts_eventually (a : ℕ) (r : CutRing) (m : ℕ)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm : 15 ≤ m+1) (hm' : 2 ≤ m) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ ρ : (Set.range (polygonAssignment (initialTest a r)) →
          alternatingGroup (Fin (m+1))) →*
          BoundedRelationCover M (alternatingGenerator a r m hm'),
        (coverMap M (alternatingGenerator a r m hm')).comp ρ =
          actualPolygonTableHom (initialTest a r) ∧
        Function.Injective ρ ∧
        ∀ b, ρ (polygonTableInput (initialTest a r) b.1
            (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1)))) =
          PresentedGroup.of (sourceConditionalLabel m b) := by
  let β := Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
      σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}
  let input : β → (Set.range (polygonAssignment (initialTest a r)) →
      alternatingGroup (Fin (m+1))) := fun b =>
    polygonTableInput (initialTest a r) b.1 ⟨b.2.val,b.2.property.1⟩
  let w : β → FreeGroup (SourceGeneratorLabel m) :=
    fun b => FreeGroup.of (sourceConditionalLabel m b)
  have hw : ∀ b, FreeGroup.lift (alternatingGenerator a r m hm') (w b) =
      actualPolygonTableHom (initialTest a r) (input b) := by
    intro b
    rw [show w b = FreeGroup.of (sourceConditionalLabel m b) from rfl,
      FreeGroup.lift_apply_of]
    change _ = actualPolygonTableHom (initialTest a r)
      (polygonTableInput (initialTest a r) b.1 ⟨b.2.val,b.2.property.1⟩)
    rw [actualPolygonTableHom_input]
    rfl
  obtain ⟨L,hL⟩ := finite_table_with_inputs_eventually (alternatingGenerator a r m hm')
    (actualPolygonTableHom (initialTest a r)) input w hw
    (alternatingGenerator_surjective a r m hr hm hm')
  refine ⟨L,fun M hM => ?_⟩
  obtain ⟨ρ,hρ,hi⟩ := hL M hM
  refine ⟨ρ,hρ,?_,hi⟩
  intro s t hst
  apply actualPolygonTableHom_injective (initialTest a r)
  have hst' := congrArg (coverMap M (alternatingGenerator a r m hm')) hst
  exact (DFunLike.congr_fun hρ s).symm.trans (hst'.trans (DFunLike.congr_fun hρ t))

end SourceInitialPointwiseTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FiniteCovariance

variable {α β ι C G : Type*} [Finite β] [Finite ι] [Group C] [Finite C] [Group G]

theorem finite_covariance_eventually (f : α → G)
    (c : C →* G) (W : C → FreeGroup α) (hW : ∀ s, FreeGroup.lift f (W s) = c s)
    (w : β → FreeGroup α) (v : ι → FreeGroup α)
    (ht : ∀ i j, Commute (FreeGroup.lift f (w i)) (FreeGroup.lift f (w j)))
    (R : C → Multiplicative (FreeAbelianGroup β) →* Multiplicative (FreeAbelianGroup β))
    (b : C → ι → ι)
    (hx : ∀ s i, c s * FreeGroup.lift f (v i) * (c s)⁻¹ = FreeGroup.lift f (v (b s i)))
    (hR : ∀ s k, c s * commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht k *
      (c s)⁻¹ = commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht (R s k)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ c' : C →* BoundedRelationCover M f,
        (coverMap M f).comp c' = c ∧
        (∀ s, c' s = PresentedGroup.mk (shortRelations M f) (W s)) ∧
        ∀ t : Multiplicative (FreeAbelianGroup β) →* BoundedRelationCover M f,
          (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
            PresentedGroup.mk (shortRelations M f) (w i)) →
          (∀ s k, c' s*t k*(c' s)⁻¹ = t (R s k)) ∧
          (∀ s i, c' s*PresentedGroup.mk (shortRelations M f) (v i)*(c' s)⁻¹ =
            PresentedGroup.mk (shortRelations M f) (v (b s i))) := by
  classical
  let T := Multiplicative (FreeAbelianGroup β)
  let q : T →* G := commutingFamilyHom (fun j => FreeGroup.lift f (w j)) ht
  let P : FreeGroup β →* FreeGroup α := FreeGroup.lift w
  have he : (FreeGroup.lift f).comp P = q.comp (translationWordMap β) := by
    ext j
    simp only [MonoidHom.comp_apply,P,translationWordMap,FreeGroup.lift_apply_of]
    exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht j).symm
  choose V hV using fun z : C × β => translationWordMap_surjective
    (R z.1 (Multiplicative.ofAdd (FreeAbelianGroup.of z.2)))
  obtain ⟨L₁,hL₁⟩ := finite_table_lift_eventually f c W hW
  obtain ⟨L₂,hL₂⟩ := finite_word_equalities_eventually f
    (fun z : C × β => W z.1*w z.2*(W z.1)⁻¹) (fun z => P (V z)) (by
      rintro ⟨s,i⟩
      simp only [map_mul,map_inv,hW]
      have hv := DFunLike.congr_fun he (V (s,i))
      simp only [MonoidHom.comp_apply,hV] at hv
      rw [hv,← hR s]
      congr 2
      exact (commutingFamilyHom_of (fun j => FreeGroup.lift f (w j)) ht i).symm)
  obtain ⟨L₃,hL₃⟩ := finite_word_equalities_eventually f
    (fun z : C × ι => W z.1*v z.2*(W z.1)⁻¹) (fun z => v (b z.1 z.2)) (by
      intro z
      simpa only [map_mul,map_inv,hW] using hx z.1 z.2)
  refine ⟨max L₁ (max L₂ L₃),fun M hM => ?_⟩
  obtain ⟨c',hc',hcW⟩ := hL₁ M ((le_max_left _ _).trans hM)
  refine ⟨c',hc',hcW,fun t ht' => ⟨?_,?_⟩⟩
  · have he' : t.comp (translationWordMap β) =
        (PresentedGroup.mk (shortRelations M f)).comp P := by
      ext j
      simpa [translationWordMap,P] using ht' j
    intro s k
    have hh : (MulAut.conj (c' s)).toMonoidHom.comp t = t.comp (R s) := by
      apply freeAbelianHom_ext
      intro i
      change c' s*t (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c' s)⁻¹ = _
      rw [hcW,ht']
      have hv := DFunLike.congr_fun he' (V (s,i))
      simp only [MonoidHom.comp_apply,hV] at hv
      rw [MonoidHom.comp_apply,hv]
      simpa only [map_mul,map_inv] using hL₂ M
        ((le_max_left _ _).trans ((le_max_right _ _).trans hM)) (s,i)
    exact DFunLike.congr_fun hh k
  · intro s i
    rw [hcW]
    simpa only [map_mul,map_inv] using hL₃ M
      ((le_max_right _ _).trans ((le_max_right _ _).trans hM)) (s,i)

end FiniteCovariance

section SourceConstantCovariance

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem constant_conjugate_conditional (U : polygonAlgebra a)
    (s z : Equiv.Perm (Fin (m+1))) :
    conditionalHom (wholePolygon a) s * conditionalHom U z *
      (conditionalHom (wholePolygon a) s)⁻¹ = conditionalHom U (s*z*s⁻¹) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (wholePolygon a) s
    (conditionalPerm U z ((conditionalPerm (wholePolygon a) s).symm p)) =
      conditionalPerm U (s*z*s⁻¹) p
  by_cases hp : p.2 ∈ U.val <;>
    simp [conditionalPerm,wholePolygon,hp,Equiv.Perm.mul_apply]

theorem source_constant_lattice_action :
    ∃ R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)),
      ∀ s k, conditionalAlternatingHom (wholePolygon a) s *
        sourceLatticeMap a r m hm k *
        (conditionalAlternatingHom (wholePolygon a) s)⁻¹ =
          sourceLatticeMap a r m hm (R s k) := by
  classical
  let T := Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  let q := sourceLatticeMap a r m hm
  let c := conditionalAlternatingHom (a := a) (m := m+1) (wholePolygon a)
  have hb : ∀ (s : alternatingGroup (Fin (m+1))) (i : Fin m × Fin 2),
      ∃ k : T, q k = c s*q (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c s)⁻¹ := by
    intro s i
    let v : CutRing × CutRing := if i.2 = 0 then (cutTau,0) else (0,cutTau)
    obtain ⟨k,hk⟩ := sourceLatticeFullMap_difference a r m hm
      (s.val (Fin.last m)) (s.val i.1.castSucc) v
    refine ⟨k,?_⟩
    apply Subtype.ext
    change sourceLatticeFullMap a r m hm k =
      conditionalHom (wholePolygon a) s.val *
        sourceLatticeFullMap a r m hm (Multiplicative.ofAdd (FreeAbelianGroup.of i)) *
        (conditionalHom (wholePolygon a) s.val)⁻¹
    rw [hk,sourceLatticeFullMap_of]
    change trackTranslation (a := a) _ = conditionalHom (wholePolygon a) s.val *
      trackTranslation (Pi.single i.1.castSucc v - Pi.single (Fin.last m) v) *
      (conditionalHom (wholePolygon a) s.val)⁻¹
    rw [constant_conjugate_translation]
    congr 1
    funext j
    simp only [Pi.sub_apply,Pi.single_apply]
    congr 1 <;> congr 1 <;> exact propext (Equiv.symm_apply_eq s.val).symm
  choose B hB using hb
  let R := fun s => commutingFamilyHom (B s) (fun _ _ => Commute.all _ _)
  refine ⟨R,fun s k => ?_⟩
  have he : (MulAut.conj (c s)).toMonoidHom.comp q = q.comp (R s) := by
    apply freeAbelianHom_ext
    intro i
    rw [MonoidHom.comp_apply,MonoidHom.comp_apply]
    change c s*q (Multiplicative.ofAdd (FreeAbelianGroup.of i))*(c s)⁻¹ =
      q ((commutingFamilyHom (B s) (fun _ _ => Commute.all _ _))
        (Multiplicative.ofAdd (FreeAbelianGroup.of i)))
    rw [commutingFamilyHom_of,hB]
  exact DFunLike.congr_fun he k

theorem source_constant_covariance_eventually
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M →
      ∃ c : alternatingGroup (Fin (m+1)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
        (coverMap M (alternatingGenerator a r m hm)).comp c =
          conditionalAlternatingHom (wholePolygon a) ∧
        (∀ b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
          σ.support.card ≤ 5}, c ⟨b.val,b.property.1⟩ =
            PresentedGroup.of (sourceConditionalLabel m (0,b))) ∧
        ∃ R : alternatingGroup (Fin (m+1)) →
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          Multiplicative (FreeAbelianGroup (Fin m × Fin 2)),
        ∀ t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
          BoundedRelationCover M (alternatingGenerator a r m hm),
          (∀ i, t (Multiplicative.ofAdd (FreeAbelianGroup.of i)) =
            PresentedGroup.of (Sum.inr i)) →
          (∀ s k, c s*t k*(c s)⁻¹ = t (R s k)) ∧
          (∀ s (b : SmallConditional m), c s*PresentedGroup.of (Sum.inl b)*(c s)⁻¹ =
            PresentedGroup.of (Sum.inl (reindexSmallConditional m s b))) := by
  classical
  let f := alternatingGenerator a r m hm
  let c := conditionalAlternatingHom (a := a) (m := m+1) (wholePolygon a)
  choose W hW using fun s => alternatingGenerator_surjective a r m hr hm' hm (c s)
  obtain ⟨R,hR⟩ := source_constant_lattice_action a r m hm
  obtain ⟨L,hL⟩ := finite_covariance_eventually f c W hW
    (fun i : Fin m × Fin 2 => FreeGroup.of (show SourceGeneratorLabel m from Sum.inr i))
    (fun b : SmallConditional m => FreeGroup.of (show SourceGeneratorLabel m from Sum.inl b))
    (fun i j => by
      change Commute (f (Sum.inr i)) (f (Sum.inr j))
      exact source_translation_commute a r m hm i j)
    R (reindexSmallConditional m) (by
      intro s b
      change c s*f (Sum.inl b)*(c s)⁻¹ = f (Sum.inl (reindexSmallConditional m s b))
      apply Subtype.ext
      exact constant_conjugate_conditional a m (initialTest a r b.1) s.val b.2.val)
    hR
  obtain ⟨L₀,hL₀⟩ := finite_word_equalities_eventually f
    (fun b : {σ : Equiv.Perm (Fin (m+1)) // σ ∈ alternatingGroup (Fin (m+1)) ∧
      σ.support.card ≤ 5} => W ⟨b.val,b.property.1⟩)
    (fun b => FreeGroup.of (sourceConditionalLabel m (0,b))) (by
      intro b
      rw [hW,FreeGroup.lift_apply_of]
      rfl)
  refine ⟨max L L₀,fun M hM => ?_⟩
  obtain ⟨c',hc',hcW,hc⟩ := hL M ((le_max_left _ _).trans hM)
  refine ⟨c',hc',?_,R,hc⟩
  intro b
  rw [hcW]
  exact hL₀ M ((le_max_right _ _).trans hM) b

end SourceConstantCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AlignedCovariance
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
section AlignedCovariance

variable {A B H : Type*} [Group A] [Group H]

theorem alignedGroup_reindex (t : A →* H) (x : B → H) (P Q : B → Prop)
    (c : H) (R : A →* A) (b : B → B)
    (ht : ∀ u, c*t u*c⁻¹ = t (R u)) (hx : ∀ i, c*x i*c⁻¹ = x (b i))
    (hb : ∀ i, P i → Q (b i)) {y : H} (hy : y ∈ alignedGroup t x P) :
    c*y*c⁻¹ ∈ alignedGroup t x Q := by
  let f : H →* H := (MulAut.conj c).toMonoidHom
  have hh : alignedGroup t x P ≤ (alignedGroup t x Q).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨i,hi,u,rfl⟩
    change c*(t u*x i*(t u)⁻¹)*c⁻¹ ∈ alignedGroup t x Q
    have he : c*(t u*x i*(t u)⁻¹)*c⁻¹ = t (R u)*x (b i)*(t (R u))⁻¹ := by
      rw [← ht,← hx]
      group
    rw [he]
    exact alignedGroup_generator t x Q (b i) (hb i hi) (R u)
  exact hh hy

end AlignedCovariance

section SourceAlignedCovariance

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) (M : ℕ)

theorem source_aligned_constant_conjugation
    (t : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (c : alternatingGroup (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (ht : ∀ s k, c s*t k*(c s)⁻¹ = t (R s k))
    (hx : ∀ s (b : SmallConditional m), c s*PresentedGroup.of (Sum.inl b)*(c s)⁻¹ =
      PresentedGroup.of (Sum.inl (reindexSmallConditional m s b)))
    (s : alternatingGroup (Fin (m+1))) (I : Finset (Fin (m+1)))
    {y : BoundedRelationCover M (alternatingGenerator a r m hm)}
    (hy : y ∈ sourceAlignedGroup a r m hm M t I) :
    c s*y*(c s)⁻¹ ∈ sourceAlignedGroup a r m hm M t (I.map s.val.toEmbedding) := by
  apply alignedGroup_reindex t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ I) (fun b => b.2.val.support ⊆ I.map s.val.toEmbedding)
    (c s) (R s) (reindexSmallConditional m s) (ht s) (hx s) _ hy
  intro b hb
  rw [reindexSmallConditional_support]
  exact Finset.map_subset_map.mpr hb

end SourceAlignedCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_InitialCoverSystem
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section InitialCoverSystem

theorem initialCoverSystem_eventually_oai (a : ℕ) (r : CutRing) (m : ℕ)
    (hm : 2 ≤ m) (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Nonempty (InitialCoverSystem a r m hm M) := by
  obtain ⟨L₁,hL₁⟩ := source_centralizing_translation_lifts_eventually a r m hm
  obtain ⟨L₂,hL₂⟩ := source_aligned_disjoint_eventually a r m hm (by omega)
  obtain ⟨L₃,hL₃⟩ := source_constant_covariance_eventually a r m hm hr hm'
  obtain ⟨L₄,hL₄⟩ := source_initial_table_lifts_eventually a r m hr hm' hm
  obtain ⟨L₅,hL₅⟩ := sourceCover_eventually_perfect a r m hr hm' hm
  refine ⟨L₁+L₂+L₃+L₄+L₅,fun M hM => ?_⟩
  obtain ⟨t,ht,htp,hts⟩ := hL₁ M (by omega)
  obtain ⟨t',ht',_,hd⟩ := hL₂ M (by omega)
  have he : t' = t := freeAbelianHom_ext t' t (fun i => (ht' i).trans (ht i).symm)
  subst t'
  obtain ⟨c,hcp,hcb,R,hc⟩ := hL₃ M (by omega)
  obtain ⟨hct,hcx⟩ := hc t ht
  obtain ⟨ρ,hρ,hinj,hinput⟩ := hL₄ M (by omega)
  refine ⟨{
    t := t
    c := c
    t_base := ht
    t_projection := htp
    t_stabilizers := hts
    c_projection := hcp
    c_base := hcb
    constant_aligned := ?_
    disjoint_aligned := hd
    initialTable := ρ
    initialTable_projection := hρ
    initialTable_injective := hinj
    initialTable_input := hinput
    perfect := hL₅ M (by omega) }⟩
  intro s I y hy
  exact source_aligned_constant_conjugation a r m hm M t c R hct hcx s I hy

end InitialCoverSystem

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.initialCoverSystem_eventually_oai := @OAI.SimpleAmenable.initialCoverSystem_eventually_oai
