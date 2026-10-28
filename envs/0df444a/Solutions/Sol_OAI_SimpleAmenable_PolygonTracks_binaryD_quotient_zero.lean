-- Prove2me | solution 1 for OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:10:47.78799+00:00
-- url     : https://prove2.me/submissions/5ef1c08b-4c32-44f8-9559-1140c5167652

import Mathlib
import Definitions.Def_OAIQ65Sa021

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FiniteGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
open scoped _root_.CategoryTheory _root_.CategoryTheory.Functor
variable {C : Type*} [Category* C]

lemma isEventuallyConstantFrom_of_succ (F : ℕ ⥤ C) (N : ℕ)
    (h : ∀ n, N ≤ n → _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (Nat.le_succ n)))) :
    F.IsEventuallyConstantFrom N := by
  intro n f
  have hn : N ≤ n := _root_.CategoryTheory.leOfHom f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      have hf : f = 𝟙 N := Subsingleton.elim _ _
      rw [hf, F.map_id]
      infer_instance
  | succ k ih =>
      have : _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega))) := ih _ (by omega)
      have := h (N+k) (by omega)
      have hf : f = (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega)) ≫
          (_root_.CategoryTheory.homOfLE (Nat.le_succ (N+k))) := Subsingleton.elim _ _
      rw [hf, F.map_comp]
      infer_instance
end CategoryTheory.Functor

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D E:Type} [Category.{0} D] [Category.{0} E]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma map_comp (F:C⥤D) (G:D⥤E) (q:ℕ) :
    SSet.homologyMap (nerveMap (F⋙G)) Z q=
      SSet.homologyMap (nerveMap F) Z q ≫ SSet.homologyMap (nerveMap G) Z q :=
  by
    change SSet.homologyMap (nerveMap F ≫ nerveMap G) Z q=_
    rw [SSet.homologyMap_comp]
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_GroupNerveCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite
namespace GroupNerveCoordinates

variable {G : Type} [Group G] {n : ℕ}
lemma labels_map {H:Type} [Group H] (f:G →* H)
    (F:ComposableArrows (SingleObj G) n) :
    labels ((nerveMap (SingleObj.mapHom G H f)).app (op ⦋n⦌) F) = fun i=>f (labels F i) := by
  funext i
  exact (map_inv f _).symm
end GroupNerveCoordinates

end

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite AlgebraicTopology
open ProductChains
namespace FreeChains

lemma complexIso_natural {X Y:SSet} (f:X⟶Y) :
    SSet.chainComplexMap f Z ≫ (complexIso Y).hom = (complexIso X).hom ≫ chainMap f := by
  apply HomologicalComplex.Hom.ext; funext n
  exact naturalIso.hom.naturality (f.app (op ⦋n⦌))
end FreeChains
namespace GroupNerveCoordinates
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable {G H:Type} [Group G] [Group H] (f:G→*H)
lemma coordinates_natural (n:ℕ) :
    (chainMap (nerveMap f.toFunctor)).f n ≫ (chainCoordinates H n).hom =
      (chainCoordinates G n).hom ≫
        (groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro z
  change (chainCoordinates H n).hom
    (Finsupp.lmapDomain ℤ ℤ ((nerveMap f.toFunctor).app (op ⦋n⦌)) (Finsupp.single s z)) = _
  rw [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  change (chainCoordinates H n).hom
    (Finsupp.single ((nerveMap f.toFunctor).app (op ⦋n⦌) s) z) = _
  erw [coordinates_single]
  change _=(groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n
    ((chainCoordinates G n).hom (Finsupp.single s z))
  erw [coordinates_single,groupHomology.chainsMap_f_single,labels_map]
  rfl
lemma chainIso_natural :
    chainMap (nerveMap f.toFunctor) ≫ (chainIso H).hom =
      (chainIso G).hom ≫ groupHomology.chainsMap f (TransitiveInduction.trivialMap f) := by
  apply HomologicalComplex.Hom.ext; funext n
  exact coordinates_natural f n
lemma homologyIso_natural (n:ℕ) :
    SSet.homologyMap (nerveMap f.toFunctor) Z n ≫ (homologyIso H n).hom =
      (homologyIso G n).hom ≫ TrivialHomology.map f n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [←HomologicalComplex.homologyMap_comp,←HomologicalComplex.homologyMap_comp]
  congr 1
  change SSet.chainComplexMap (nerveMap f.toFunctor) Z ≫ (complexIso _).hom ≫ (chainIso H).hom =
    ((complexIso _).hom ≫ (chainIso G).hom) ≫ _
  rw [←Category.assoc,complexIso_natural,Category.assoc,chainIso_natural,←Category.assoc]
end GroupNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonStableHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.PolygonTracks

attribute [local instance 1200] Rep.hV2

lemma successor_H1_isIso (a n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (successorStabilize a n) 1) := by
  unfold successorStabilize
  rw [TrivialHomology.map_comp]
  have := PolygonPlacement.Configuration.stabilize_H1_isIso a n hn
  have := TrivialHomology.isIso_equiv (castFull a (Nat.add_comm 1 n)) 1
  infer_instance

end SimpleAmenable.PolygonTracks

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonComponentCompletion
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instEssSurjStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFullStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instIsEquivalenceStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.instBraidedStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.instFaithfulStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.instMonoidalStringGroupoidStringEval _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_braided _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonComponentCompletion

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

theorem component_complement (U : PolygonObject a) :
    component U * component (complement U)=component (standard a U.tracks) := by
  rw [←component_sum]
  exact congr_toSkeleton_of_iso (complementIso U)

end PolygonObject
end PolygonComponentCompletion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instBraidedStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalStringGroupoidToStrings _root_.OAI.SimpleAmenable.PolygonObject.Labelled.reindexStringMonoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_braided _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma componentGenerator_cofinal (a:ℕ) : ∀p:Skeleton (PolygonObject a),∃q n,p*q=componentGenerator a^n := by
  intro p
  let U:=ComponentTranslation.repr p
  refine ⟨PolygonObject.component (PolygonObject.complement U), U.tracks,?_⟩
  have h:=PolygonObject.component_complement U
  rw [PolygonObject.component_standard_pow] at h
  simpa only [U,PolygonObject.component,repr_component] using h
end SimpleAmenable.PolygonTracks
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

lemma component_successor_isIso (a n q:ℕ) [IsIso (TrivialHomology.map (successorStabilize a n) q)] :
    IsIso (SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
  have sourceInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a n) Z q
  have targetInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a (n+1)) Z q
  have hg:=GroupNerveCoordinates.homologyIso_natural (successorStabilize a n) q
  have successorIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q) := by
    have successorCompositeIso : IsIso (SSet.homologyMap (nerveMap (successorStabilize a n).toFunctor) Z q ≫
      (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom) := by rw [hg]; infer_instance
    exact (isIso_comp_right_iff _ (GroupNerveCoordinates.homologyIso (polygonFullGroup a (n+1)) q).hom).mp inferInstance
  have h:=(NerveHomotopy.ofNatTrans (fiberSuccessorIso a n).hom).congr_homologyMap Z q
  rw [ComponentStable.map_comp,ComponentStable.map_comp] at h
  have inclusionCompositeIso : IsIso (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q ≫
    SSet.homologyMap (nerveMap
      (ComponentTranslation.translate (componentGenerator a) (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q) := by
    rw [h]
    infer_instance
  exact (isIso_comp_left_iff (SSet.homologyMap (nerveMap (standardFiberInclusion a n)) Z q) _).mp inferInstance
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected_one _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainTensor
open FreeChains

variable (S T:ShortComplex (ChainComplex A ℕ)) (s:S.Splitting) (t:T.Splitting)
lemma homology_joint_kernel' (n:ℕ) (x:(S.X₂⊗T.X₂).homology n)
    (h0:homologyMap (s.r⊗ₘt.r) n x=0)
    (h1:homologyMap (𝟙 S.X₂⊗ₘT.g) n x=0)
    (h2:homologyMap (S.g⊗ₘ𝟙 T.X₂) n x=0) : x=0 := by
  have hid := congrArg (fun f => homologyMap f n) (splitting_tensor_identity S T s t)
  simp only [homologyMap_add,homologyMap_comp,homologyMap_id] at hid
  have hh := congrArg (fun f => f x) hid
  change homologyMap (S.f⊗ₘT.f) n (homologyMap (s.r⊗ₘt.r) n x) +
    homologyMap ((s.r≫S.f)⊗ₘt.s) n (homologyMap (𝟙 S.X₂⊗ₘT.g) n x) +
    homologyMap (s.s⊗ₘ𝟙 T.X₂) n (homologyMap (S.g⊗ₘ𝟙 T.X₂) n x) = x at hh
  simpa only [h0,h1,h2,map_zero,add_zero] using hh.symm
end ChainTensor

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

attribute [local instance 1200] Submodule.module
variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
lemma projection_joint_zero (n:ℕ) (x:((X⊗Y).homology Z n : A))
    (hx:projection X Y n x=0) (hr:redProjection X Y n x=0) : x=0 := by
  have hf : SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.fst : X.homology Z n ⊞ Y.homology Z n ⟶ X.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.fst) x=0 at h
    simpa only [projection,biprod.lift_fst] using h
  have hg : SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.snd : X.homology Z n ⊞ Y.homology Z n ⟶ Y.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.snd) x=0 at h
    simpa only [projection,biprod.lift_snd] using h
  let e := homologyIsoN X Y n
  have h1 : homologyMap (𝟙 (complex X)⊗ₘConstantSplit.aug Y) n (e.hom x)=0 := by
    have hn := homology_natural (𝟙 X) (SSet.const (X:=Y) (Y:=one) PUnit.unit) n
    rw [chainMap_id] at hn
    have he : (𝟙 X)⊗ₘ(SSet.const (X:=Y) (Y:=one) PUnit.unit) =
        CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN X one n).hom
      (SSet.homologyMap (pairLeft X one PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x)) = _ at hh
    simpa only [hf,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have h2 : homologyMap (ConstantSplit.aug X⊗ₘ𝟙 (complex Y)) n (e.hom x)=0 := by
    have hn := homology_natural (SSet.const (X:=X) (Y:=one) PUnit.unit) (𝟙 Y) n
    rw [chainMap_id] at hn
    have he : (SSet.const (X:=X) (Y:=one) PUnit.unit)⊗ₘ(𝟙 Y) =
        CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN one Y n).hom
      (SSet.homologyMap (pairRight one Y PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x)) = _ at hh
    simpa only [hg,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have hh := ChainTensor.homology_joint_kernel' (ConstantSplit.sc X) (ConstantSplit.sc Y)
    (ConstantSplit.splitting X (point X)) (ConstantSplit.splitting Y (point Y)) n
    (e.hom x) hr h1 h2
  exact e.toLinearEquiv.injective (hh.trans (map_zero e.toLinearEquiv).symm)
end ConnectedProduct

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonFixedReturn
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
lemma component_sequence_succ (a n q:ℕ) :
    (homologyDiagram (C:=PolygonObject a) q).map
      ((CofinalPowers.sequence (componentGenerator a)).map (homOfLE (Nat.le_succ n))) =
        SSet.homologyMap (nerveMap (ComponentTranslation.translate (componentGenerator a)
          (componentGenerator a^n) (componentGenerator a^(n+1)) (pow_succ' _ _).symm)) Z q := by
  change SSet.homologyMap (nerveMap (ComponentTranslation.translate
    (componentGenerator a ^ (n+1-n)) _ _ _)) Z q = _
  simp only [Nat.add_sub_cancel_left,pow_one]
  rfl
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NerveProduct
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentTranslation.fiber_nerve_connected _root_.OAI.ComponentTranslation.fiber_nonempty _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma tensorLeft_stable (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q=toStable (C:=C) q := by
  apply (ComponentCoproduct.homologyIsColimit C q).hom_ext
  intro p
  change inclusion p.as q ≫ (SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q)=inclusion p.as q ≫ toStable q
  let e : (property p.as).ι ⋙ tensorLeft U ≅
      translate (toSkeleton U) p.as (toSkeleton U*p.as) rfl ⋙ (property (toSkeleton U*p.as)).ι :=
    (Functor.isoWhiskerLeft (property p.as).ι ((tensoringLeft C).mapIso (reprObjectIso U))).symm
  have h:=(NerveHomotopy.ofNatTrans e.hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (property p.as).ι ≫ nerveMap (tensorLeft U)) Z q =
    SSet.homologyMap (nerveMap (translate (toSkeleton U) p.as (toSkeleton U*p.as) rfl) ≫ nerveMap (property (toSkeleton U*p.as)).ι) Z q at h
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp] at h
  change inclusion p.as q ≫ (SSet.homologyMap (nerveMap (tensorLeft U)) Z q ≫ toStable q)=_
  rw [←Category.assoc]
  change (SSet.homologyMap (nerveMap (property p.as).ι) Z q ≫ SSet.homologyMap (nerveMap (tensorLeft U)) Z q) ≫ toStable q = _
  rw [h,Category.assoc]
  exact translate_toStable _ _ _ rfl q
lemma tensorRight_stable (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorRight U)) Z q ≫ toStable q=toStable (C:=C) q := by
  have h:=(NerveHomotopy.ofNatTrans (BraidedCategory.tensorLeftIsoTensorRight U).hom).congr_homologyMap Z q
  rw [←h,tensorLeft_stable]
omit [SymmetricCategory C] in
@[reassoc] lemma multiplication_left (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) Z q ≫
      SSet.homologyMap multiplication Z q ≫ toStable q =
        SSet.homologyMap (multiplication (C:=C)) Z q ≫ toStable q := by
  apply (cancel_epi (SSet.homologyMap (NerveProduct.iso C C).hom Z q)).mp
  rw [←SSet.homologyMap_comp_assoc]
  have he : (NerveProduct.iso C C).hom ≫ (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) =
      nerveMap ((tensorLeft U).prod (𝟭 C)) ≫ (NerveProduct.iso C C).hom := rfl
  have hm : (NerveProduct.iso C C).hom ≫ multiplication=nerveMap tensorFunctor := by simp [multiplication]
  rw [he,SSet.homologyMap_comp_assoc]
  rw [←SSet.homologyMap_comp_assoc (f:=(NerveProduct.iso C C).hom) (g:=multiplication),hm]
  rw [←SSet.homologyMap_comp_assoc]
  have h:=(NerveHomotopy.ofNatTrans (leftTensorIso U).hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (((tensorLeft U).prod (𝟭 C)) ⋙ tensorFunctor)) Z q ≫ toStable q = _
  rw [h,map_comp,Category.assoc,tensorLeft_stable]
@[reassoc] lemma multiplication_right (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q ≫
      SSet.homologyMap multiplication Z q ≫ toStable q =
        SSet.homologyMap (multiplication (C:=C)) Z q ≫ toStable q := by
  apply (cancel_epi (SSet.homologyMap (NerveProduct.iso C C).hom Z q)).mp
  rw [←SSet.homologyMap_comp_assoc]
  have he : (NerveProduct.iso C C).hom ≫ (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) =
      nerveMap ((𝟭 C).prod (tensorRight U)) ≫ (NerveProduct.iso C C).hom := rfl
  have hm : (NerveProduct.iso C C).hom ≫ multiplication=nerveMap tensorFunctor := by simp [multiplication]
  rw [he,SSet.homologyMap_comp_assoc]
  rw [←SSet.homologyMap_comp_assoc (f:=(NerveProduct.iso C C).hom) (g:=multiplication),hm]
  rw [←SSet.homologyMap_comp_assoc]
  have h:=(NerveHomotopy.ofNatTrans (rightTensorIso U).hom).congr_homologyMap Z q
  change SSet.homologyMap (nerveMap (((𝟭 C).prod (tensorRight U)) ⋙ tensorFunctor)) Z q ≫ toStable q = _
  rw [h,map_comp,Category.assoc,tensorRight_stable]
end ComponentStable

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveProduct
open FreeChains

variable {C D E F:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E] [Category.{0} F]
lemma homology_congr {f f':C⥤E} {g g':D⥤F} (α:f≅f') (β:g≅g') (q:ℕ) :
    SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z q=SSet.homologyMap (nerveMap f'⊗ₘnerveMap g') Z q := by
  apply (cancel_epi (SSet.homologyMap (iso C D).hom Z q)).mp
  rw [←SSet.homologyMap_comp,←natural,←SSet.homologyMap_comp,←natural,
    SSet.homologyMap_comp,SSet.homologyMap_comp]
  rw [(NerveHomotopy.ofNatTrans (NatIso.prod α β).hom).congr_homologyMap Z q]
end NerveProduct
namespace ComponentStable
open FreeChains ComponentTranslation ConnectedProduct

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma binaryD_left (U:C) (q:ℕ) :
    SSet.homologyMap (nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  let f:=nerveMap (tensorLeft U)⊗ₘ𝟙 (nerve C)
  have hf : f≫CartesianMonoidalCategory.fst _ _=CartesianMonoidalCategory.fst _ _≫nerveMap (tensorLeft U) := rfl
  have hg : f≫CartesianMonoidalCategory.snd _ _=CartesianMonoidalCategory.snd _ _ := rfl
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [multiplication_left,←SSet.homologyMap_comp_assoc,hf,SSet.homologyMap_comp_assoc,tensorLeft_stable,
    ←SSet.homologyMap_comp_assoc,hg]
@[reassoc] lemma binaryD_right (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  let f:=𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)
  have hf : f≫CartesianMonoidalCategory.fst _ _=CartesianMonoidalCategory.fst _ _ := rfl
  have hg : f≫CartesianMonoidalCategory.snd _ _=CartesianMonoidalCategory.snd _ _≫nerveMap (tensorRight U) := rfl
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [multiplication_right,←SSet.homologyMap_comp_assoc,hf,←SSet.homologyMap_comp_assoc,hg,
    SSet.homologyMap_comp_assoc,tensorRight_stable]
@[reassoc] lemma binaryD_second_left (U:C) (q:ℕ) :
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorLeft U)) Z q ≫ binaryD q=binaryD (C:=C) q := by
  have h:=NerveProduct.homology_congr (Iso.refl (𝟭 C)) (BraidedCategory.tensorLeftIsoTensorRight U) q
  change SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorLeft U)) Z q =
    SSet.homologyMap (𝟙 (nerve C)⊗ₘnerveMap (tensorRight U)) Z q at h
  rw [h,binaryD_right]
omit [SymmetricCategory C] in
lemma pairLeft_multiplication (U:C) :
    pairLeft (nerve C) (nerve C) (nerveEquiv.symm U) ≫ multiplication=nerveMap (tensorRight U) := by
  apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro F
  apply CategoryTheory.Functor.ext
  · intro x y f
    change (F.map f ⊗ₘ 𝟙 U) = 𝟙 _ ≫ (F.map f ▷ U) ≫ 𝟙 _
    simp
  · intro x; rfl
omit [SymmetricCategory C] in
lemma pairRight_multiplication (U:C) :
    pairRight (nerve C) (nerve C) (nerveEquiv.symm U) ≫ multiplication=nerveMap (tensorLeft U) := by
  apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro F
  apply CategoryTheory.Functor.ext
  · intro x y f
    change (𝟙 U ⊗ₘ F.map f) = 𝟙 _ ≫ (U ◁ F.map f) ≫ 𝟙 _
    simp
  · intro x; rfl
@[reassoc] lemma pairLeft_binaryD (v:(nerve C).obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (pairLeft (nerve C) (nerve C) v) Z q ≫ binaryD q=0 := by
  obtain ⟨U,rfl⟩:=nerveEquiv.symm.surjective v
  have constant_zero : SSet.homologyMap (SSet.const (nerveEquiv.symm U) : nerve C ⟶ nerve C) Z q = 0 :=
    const_homology_zero _ q hq
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,
    pairLeft_multiplication]
  simp only [pairLeft,CartesianMonoidalCategory.lift_fst,CartesianMonoidalCategory.lift_snd,
    SSet.homologyMap_id,constant_zero,Category.id_comp,zero_comp,add_zero,tensorRight_stable,sub_self]
omit [SymmetricCategory C] in
@[reassoc] lemma pairRight_binaryD (v:(nerve C).obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (pairRight (nerve C) (nerve C) v) Z q ≫ binaryD q=0 := by
  obtain ⟨U,rfl⟩:=nerveEquiv.symm.surjective v
  have constant_zero : SSet.homologyMap (SSet.const (nerveEquiv.symm U) : nerve C ⟶ nerve C) Z q = 0 :=
    const_homology_zero _ q hq
  simp only [binaryD,Preadditive.comp_add,Preadditive.comp_sub,Preadditive.add_comp,Preadditive.sub_comp]
  rw [←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc,
    pairRight_multiplication]
  simp only [pairRight,CartesianMonoidalCategory.lift_fst,CartesianMonoidalCategory.lift_snd,
    SSet.homologyMap_id,constant_zero,Category.id_comp,zero_comp,zero_add,tensorLeft_stable,sub_self]
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BinaryPullback
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation ConnectedProduct

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X Y X' Y':SSet}
omit [SymmetricCategory C] in
lemma pullD_congr {D E:Type} [Category.{0} D] [Category.{0} E]
    {f f':D⥤C} {g g':E⥤C} (α:f≅f') (β:g≅g') (q:ℕ) :
    pullD (nerveMap f) (nerveMap g) q=pullD (nerveMap f') (nerveMap g') q := by
  rw [pullD,pullD,NerveProduct.homology_congr α β]
omit [SymmetricCategory C] in
lemma pullD_left (f:X⟶nerve C) (g:Y⟶nerve C) (U:C) (q:ℕ) :
    pullD (f≫nerveMap (tensorLeft U)) g q=pullD f g q := by
  conv_lhs => rw [←Category.comp_id g]
  rw [pullD,←tensorHom_comp_tensorHom,SSet.homologyMap_comp,Category.assoc,binaryD_left]
  rfl
lemma pullD_right (f:X⟶nerve C) (g:Y⟶nerve C) (U:C) (q:ℕ) :
    pullD f (g≫nerveMap (tensorLeft U)) q=pullD f g q := by
  conv_lhs => rw [←Category.comp_id f]
  rw [pullD,←tensorHom_comp_tensorHom,SSet.homologyMap_comp,Category.assoc,binaryD_second_left]
  rfl
lemma pairLeft_tensor (f:X⟶X') (g:Y⟶Y') (y:Y.obj (op ⦋0⦌)) :
    pairLeft X Y y ≫ (f⊗ₘg)=f≫pairLeft X' Y' (g.app _ y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [pairLeft]
  · simp [pairLeft,SSet.const_comp]
lemma pairRight_tensor (f:X⟶X') (g:Y⟶Y') (x:X.obj (op ⦋0⦌)) :
    pairRight X Y x ≫ (f⊗ₘg)=g≫pairRight X' Y' (f.app _ x) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [pairRight,SSet.const_comp]
  · simp [pairRight]
@[reassoc] lemma inclusion_pullD (f:X⟶nerve C) (g:Y⟶nerve C)
    (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0) :
    ConnectedProduct.inclusion X Y x y q ≫ pullD f g q=0 := by
  apply biprod.hom_ext'
  · simp only [ConnectedProduct.inclusion,biprod.inl_desc_assoc,pullD]
    rw [←SSet.homologyMap_comp_assoc,pairLeft_tensor,SSet.homologyMap_comp_assoc,pairLeft_binaryD _ q hq,comp_zero]
    simp
  · simp only [ConnectedProduct.inclusion,biprod.inr_desc_assoc,pullD]
    rw [←SSet.homologyMap_comp_assoc,pairRight_tensor,SSet.homologyMap_comp_assoc,pairRight_binaryD _ q hq,comp_zero]
    simp
lemma pullD_kernel_value (f:X⟶nerve C) (g:Y⟶nerve C)
    (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (q:ℕ) (hq:q≠0)
    (z:((X⊗Y).homology Z q:A)) :
    ∃w:((X⊗Y).homology Z q:A), projection X Y q w=0 ∧ pullD f g q w=pullD f g q z := by
  let inc:=ConnectedProduct.inclusion X Y x y q
  refine ⟨z-inc (projection X Y q z),?_,?_⟩
  · rw [map_sub]
    have h:=congrArg (fun k=>k (projection X Y q z)) (inclusion_projection X Y x y q hq)
    change projection X Y q (inc (projection X Y q z))=projection X Y q z at h
    rw [h,sub_self]
  · rw [map_sub]
    have h:=congrArg (fun k=>k (projection X Y q z)) (inclusion_pullD f g x y q hq)
    change pullD f g q (inc (projection X Y q z))=0 at h
    rw [h,sub_zero]
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorTwo
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.leftAdditive _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.ChainTensor.rightAdditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ReducedTensorTwo

section
open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
include hK hL
lemma inc_epi : Epi (inc K L 1 1 2 rfl) where
  left_cancellation f g h := by
    apply total.hom_ext
    intro p q hpq
    change inc K L p q 2 hpq ≫ f=inc K L p q 2 hpq ≫ g
    have hpq':p+q=2:=hpq
    by_cases hp:p=0
    · subst p; exact (Functor.map_isZero (tensorRight (L.X q)) hK).eq_of_src _ _
    · by_cases hq:q=0
      · subst q; exact (Functor.map_isZero (tensorLeft (K.X p)) hL).eq_of_src _ _
      · have he:p=1:=by omega
        have he':q=1:=by omega
        subst p q
        exact h
lemma raw_epi : Epi (raw K L hK hL) := by
  have :=inc_epi K L hK hL
  dsimp only [raw]; infer_instance
end

open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
lemma generator_epi : Epi (generator K L hK hL) := by
  have : Epi ((πK K hK ⊗ₘ πL L hL) ≫ generator K L hK hL):=by
    rw [π_generator]; exact raw_epi K L hK hL
  exact epi_of_epi (πK K hK ⊗ₘ πL L hL) _
end ReducedTensorTwo

end

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ModuleCat
open scoped _root_.ModuleCat
lemma tensor_epi {R:Type} [CommRing R] {M N P Q:ModuleCat.{0} R} (f:M⟶N) (g:P⟶Q)
    [Epi f] [Epi g] : Epi (f⊗ₘg) := by
  apply (_root_.ModuleCat.epi_iff_surjective _).mpr
  exact TensorProduct.map_surjective ((_root_.ModuleCat.epi_iff_surjective f).mp inferInstance)
    ((_root_.ModuleCat.epi_iff_surjective g).mp inferInstance)
end ModuleCat
namespace ReducedTensorTwo
open FreeChains

variable {K L K' L':ChainComplex A ℕ} (f:K⟶K') (g:L⟶L')
variable (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0)) (hK':IsZero (K'.X 0)) (hL':IsZero (L'.X 0))
@[reassoc] lemma generator_natural : generator K L hK hL ≫ homologyMap (f⊗ₘg) 2=
    (homologyMap f 1⊗ₘhomologyMap g 1) ≫ generator K' L' hK' hL' := by
  have :=ModuleCat.tensor_epi (πK K hK) (πL L hL)
  apply (cancel_epi (πK K hK⊗ₘπL L hL)).mp
  rw [π_generator_assoc,raw_natural,←Category.assoc,tensorHom_comp_tensorHom]
  rw [ChainComplex.positiveπ_natural f 0 _ (hK'.eq_of_tgt _ _),
    ChainComplex.positiveπ_natural g 0 _ (hL'.eq_of_tgt _ _),←tensorHom_comp_tensorHom,
    Category.assoc,π_generator]
include hK hL hK' hL' in
lemma homology_epi [Epi (homologyMap f 1)] [Epi (homologyMap g 1)] :
    Epi (homologyMap (f⊗ₘg) 2) := by
  have :=ModuleCat.tensor_epi (homologyMap f 1) (homologyMap g 1)
  have :=generator_epi K' L' hK' hL'
  have : Epi (generator K L hK hL ≫ homologyMap (f⊗ₘg) 2):=by rw [generator_natural f g hK hL hK' hL']; infer_instance
  exact epi_of_epi (generator K L hK hL) _
end ReducedTensorTwo

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedNatural
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConstantSplit
open FreeChains ProductChains

variable {X Y:SSet}
lemma redMap_epi (f:X⟶Y) (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (n:ℕ) (hn:n≠0)
    [chainMapEpi : Epi (homologyMap (chainMap f) n)] : Epi (homologyMap (redMap f) n) := by
  have h:=congrArg (fun f=>homologyMap f n) (redMap_inclusion f)
  erw [homologyMap_comp (redMap f) (sc Y).f,
    homologyMap_comp (sc X).f (chainMap f)] at h
  have : IsIso (homologyMap (sc X).f n):=(inclusionIso X x n hn).isIso_hom
  have : IsIso (homologyMap (sc Y).f n):=(inclusionIso Y y n hn).isIso_hom
  have : Epi (homologyMap (redMap f) n ≫ homologyMap (sc Y).f n):=by
    erw [h]
    exact epi_comp' (inferInstanceAs (Epi (homologyMap (sc X).f n))) chainMapEpi
  exact (epi_comp_iff_of_isIso _ (homologyMap (sc Y).f n)).mp inferInstance
lemma red_X_zero (X:SSet) [Subsingleton (X.obj (op ⦋0⦌))] (x:X.obj (op ⦋0⦌)) :
    IsZero (((sc X).X₁).X 0) := by
  have he : (aug X).f 0 ≫ (sec X x).f 0=𝟙 ((complex X).X 0) := by
    change (ModuleCat.free ℤ).map ((SSet.const (Y:=one) PUnit.unit).app (op ⦋0⦌)) ≫
      (ModuleCat.free ℤ).map ((SSet.const (X:=one) x).app (op ⦋0⦌))=𝟙 _
    rw [←Functor.map_comp,←(ModuleCat.free ℤ).map_id (X.obj (op ⦋0⦌))]
    congr 1
    ext z
    exact Subsingleton.elim _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  have : Mono ((sc X).f.f 0) := by change Mono ((kernel.ι (aug X)).f 0); infer_instance
  apply (cancel_mono ((sc X).f.f 0)).mp
  simp only [Category.id_comp,zero_comp]
  have h:=congrArg (fun f=>f.f 0) (sc X).zero
  simp only [HomologicalComplex.comp_f,HomologicalComplex.zero_f] at h
  have hh:=congrArg (fun f=>f≫(sec X x).f 0) h
  change ((sc X).f.f 0 ≫ (aug X).f 0) ≫ (sec X x).f 0 = _ at hh
  erw [Category.assoc,he,zero_comp] at hh
  change (kernel.ι (aug X)).f 0 ≫ 𝟙 ((complex X).X 0)=0 at hh
  rw [Category.comp_id] at hh
  exact hh
end ConstantSplit

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains ConstantSplit

variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
lemma red_projection_recover (n:ℕ) (x:((X⊗Y).homology Z n : A))
    (hx:projection X Y n x=0) : redInclusion X Y n (redProjection X Y n x)=x := by
  apply sub_eq_zero.mp
  apply projection_joint_zero X Y n
  · rw [map_sub,hx,sub_zero]
    change (redInclusion X Y n≫projection X Y n) _=0
    rw [redInclusion_projection]; rfl
  · rw [map_sub]
    change (redInclusion X Y n≫redProjection X Y n) _ - _=0
    rw [redInclusion_redProjection]
    exact sub_self _
variable {X Y} {X' Y':SSet} [X'.IsConnected] [Y'.IsConnected]
lemma kernel_map_surjective (f:X⟶X') (g:Y⟶Y')
    [Subsingleton (X.obj (op ⦋0⦌))] [Subsingleton (Y.obj (op ⦋0⦌))]
    [Subsingleton (X'.obj (op ⦋0⦌))] [Subsingleton (Y'.obj (op ⦋0⦌))]
    [Epi (SSet.homologyMap f Z 1)] [Epi (SSet.homologyMap g Z 1)]
    (x:((X'⊗Y').homology Z 2 : A)) (hx:projection X' Y' 2 x=0) :
    ∃y:((X⊗Y).homology Z 2 : A), projection X Y 2 y=0 ∧ SSet.homologyMap (f⊗ₘg) Z 2 y=x := by
  have hf:=FreeChains.complexIso_natural f
  have : Epi (homologyMap (chainMap f) 1) := by
    have hh:=congrArg (fun k=>homologyMap k 1) hf
    simp only [homologyMap_comp] at hh
    have : Epi (homologyMap (FreeChains.complexIso X).hom 1 ≫ homologyMap (chainMap f) 1):=by rw [←hh]; infer_instance
    exact epi_of_epi (homologyMap (FreeChains.complexIso X).hom 1) _
  have : Epi (homologyMap (chainMap g) 1) := by
    have hh:=congrArg (fun k=>homologyMap k 1) (FreeChains.complexIso_natural g)
    simp only [homologyMap_comp] at hh
    have : Epi (homologyMap (FreeChains.complexIso Y).hom 1 ≫ homologyMap (chainMap g) 1):=by rw [←hh]; infer_instance
    exact epi_of_epi (homologyMap (FreeChains.complexIso Y).hom 1) _
  have :=redMap_epi f (point X) (point X') 1 (by decide)
  have :=redMap_epi g (point Y) (point Y') 1 (by decide)
  have :=ReducedTensorTwo.homology_epi (redMap f) (redMap g)
    (red_X_zero X (point X)) (red_X_zero Y (point Y))
    (red_X_zero X' (point X')) (red_X_zero Y' (point Y'))
  obtain ⟨y,hy⟩:=((ModuleCat.epi_iff_surjective (homologyMap (redMap f⊗ₘredMap g) 2)).mp inferInstance) (redProjection X' Y' 2 x)
  refine ⟨redInclusion X Y 2 y,?_,?_⟩
  · change (redInclusion X Y 2≫projection X Y 2) y=0
    rw [redInclusion_projection]; rfl
  · change (redInclusion X Y 2≫SSet.homologyMap (f⊗ₘg) Z 2) y=x
    rw [redInclusion_natural]
    change redInclusion X' Y' 2 (homologyMap (redMap f⊗ₘredMap g) 2 y)=x
    rw [hy,red_projection_recover X' Y' 2 x hx]
end ConnectedProduct

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageBinary
attribute [-instance] _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module
lemma stageTranslate_H1_iso (a m:ℕ) (hm:32 ≤ m) :
    IsIso (SSet.homologyMap (nerveMap (stageTranslate a m hm)) Z 1) := by
  let F:=CofinalPowers.sequence (componentGenerator a) ⋙ homologyDiagram (C:=PolygonObject a) 1
  have h: F.IsEventuallyConstantFrom 32 := Functor.isEventuallyConstantFrom_of_succ F 32 (by
    intro n hn
    change IsIso ((homologyDiagram (C:=PolygonObject a) 1).map
      ((CofinalPowers.sequence (componentGenerator a)).map (homOfLE (Nat.le_succ n))))
    rw [component_sequence_succ]
    have successorIso := successor_H1_isIso a n hn
    exact component_successor_isIso a n 1)
  exact h (homOfLE hm)
lemma fixedToStage_H1_iso (a m:ℕ) (hm:32 ≤ m) :
    IsIso (SSet.homologyMap (nerveMap (fixedToStage a m hm)) Z 1) := by
  have sourceInclusionIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a 32) Z 1
  have targetInverseIso := NerveHomotopy.homologyMap_isIso (standardFiberInclusion a m).asEquivalence.inverse Z 1
  have translationIso := stageTranslate_H1_iso a m hm
  change IsIso (SSet.homologyMap
    (nerveMap (standardFiberInclusion a 32) ≫ nerveMap (stageTranslate a m hm) ≫
      nerveMap (standardFiberInclusion a m).asEquivalence.inverse) Z 1)
  simp only [SSet.homologyMap_comp]
  infer_instance
lemma stage_pullD (a n m:ℕ) (hn:32 ≤ n) (hm:32 ≤ m) :
    SSet.homologyMap (nerveMap (fixedToStage a n hn)⊗ₘnerveMap (fixedToStage a m hm)) Z 2 ≫
      pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 =
        pullD (nerveMap (standardNerveInclusion a 32)) (nerveMap (standardNerveInclusion a 32)) 2 := by
  rw [pullD_comp]
  change pullD (nerveMap (fixedToStage a n hn ⋙ standardNerveInclusion a n))
    (nerveMap (fixedToStage a m hm ⋙ standardNerveInclusion a m)) 2 = _
  rw [pullD_congr (fixedToStageGlobal a n hn) (fixedToStageGlobal a m hm)]
  change pullD (nerveMap (standardNerveInclusion a 32) ≫ nerveMap (tensorLeft _))
    (nerveMap (standardNerveInclusion a 32) ≫ nerveMap (tensorLeft _)) 2 = _
  rw [pullD_left,pullD_right]
lemma stage_value_mem (a n m:ℕ) (hn:32 ≤ n) (hm:32 ≤ m)
    (z:((nerve (SingleObj (polygonFullGroup a n))⊗nerve (SingleObj (polygonFullGroup a m))).homology Z 2:A)) :
    pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 z ∈ mixedImage a := by
  obtain ⟨w,hw,he⟩:=pullD_kernel_value (nerveMap (standardNerveInclusion a n))
    (nerveMap (standardNerveInclusion a m)) (nerveEquiv.symm (SingleObj.star _))
      (nerveEquiv.symm (SingleObj.star _)) 2 (by decide) z
  have leftStageIso := fixedToStage_H1_iso a n hn
  have rightStageIso := fixedToStage_H1_iso a m hm
  obtain ⟨v,hv,hve⟩:=ConnectedProduct.kernel_map_surjective
    (nerveMap (fixedToStage a n hn)) (nerveMap (fixedToStage a m hm)) w hw
  refine ⟨⟨v,hv⟩,?_⟩
  have h:=congrArg (fun f=>f v) (stage_pullD a n m hn hm)
  change pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2
    (SSet.homologyMap (nerveMap (fixedToStage a n hn)⊗ₘnerveMap (fixedToStage a m hm)) Z 2 v)=_ at h
  rw [hve] at h
  exact h.symm.trans he
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiBinary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiFiber

variable (C:Type) [Groupoid.{0} C]
lemma binary_inclusion (p:Fin 2→Skeleton C) :
    inclusion C (Fin 2) p ≫ (PiSSet.binaryIso (fun _:Fin 2=>nerve C)).hom =
      (PiSSet.binaryIso (fun i=>nerve (ComponentTranslation.Fiber (p i)))).hom ≫
        (nerveMap (ComponentTranslation.property (p 0)).ι⊗ₘnerveMap (ComponentTranslation.property (p 1)).ι) := rfl
end PiFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiberBinary
attribute [-instance] _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_full _root_.OAI.SimpleAmenable.SymmetricConfiguration.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation ComponentStable

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma large_complement (a:ℕ) (p:Skeleton (PolygonObject a)) :
    ∃n,32 ≤ n ∧ ∃r,r*p=componentGenerator a^n := by
  obtain ⟨r,k,h⟩:=componentGenerator_cofinal a p
  refine ⟨32+k,by omega,componentGenerator a^32*r,?_⟩
  rw [mul_assoc,mul_comm r p,h,pow_add]
lemma fiber_value_mem (a:ℕ) (p q:Skeleton (PolygonObject a))
    (z:((nerve (Fiber p)⊗nerve (Fiber q)).homology Z 2:A)) :
    pullD (nerveMap (property p).ι) (nerveMap (property q).ι) 2 z ∈ mixedImage a := by
  obtain ⟨n,hn,r,hr⟩:=large_complement a p
  obtain ⟨m,hm,s,hs⟩:=large_complement a q
  let f:=fiberToStage a p n r hr
  let g:=fiberToStage a q m s hs
  have h : SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z 2 ≫
      pullD (nerveMap (standardNerveInclusion a n)) (nerveMap (standardNerveInclusion a m)) 2 =
        pullD (nerveMap (property p).ι) (nerveMap (property q).ι) 2 := by
    rw [pullD_comp]
    change pullD (nerveMap (fiberToStage a p n r hr ⋙ standardNerveInclusion a n))
      (nerveMap (fiberToStage a q m s hs ⋙ standardNerveInclusion a m)) 2 = _
    rw [pullD_congr (fiberToStageGlobal a p n r hr) (fiberToStageGlobal a q m s hs)]
    change pullD (nerveMap (property p).ι ≫ nerveMap (tensorLeft _))
      (nerveMap (property q).ι ≫ nerveMap (tensorLeft _)) 2 = _
    rw [pullD_left,pullD_right]
  have hv:=stage_value_mem a n m hn hm (SSet.homologyMap (nerveMap f⊗ₘnerveMap g) Z 2 z)
  have he:=congrArg (fun k=>k z) h
  exact he ▸ hv
lemma binaryD_quotient_zero_oai (a:ℕ) : binaryD (C:=PolygonObject a) 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ=0 := by
  apply (cancel_epi (SSet.homologyMap (PiSSet.binaryIso (fun _:Fin 2=>nerve (PolygonObject a))).hom Z 2)).mp
  apply (PiFiber.homologyIsColimit (PolygonObject a) (Fin 2) 2).hom_ext
  intro p
  change SSet.homologyMap (PiFiber.inclusion (PolygonObject a) (Fin 2) p.as) Z 2 ≫
    (SSet.homologyMap (PiSSet.binaryIso (fun _:Fin 2=>nerve (PolygonObject a))).hom Z 2 ≫
      (binaryD 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ)) = _
  erw [←SSet.homologyMap_comp_assoc,PiFiber.binary_inclusion,SSet.homologyMap_comp_assoc]
  have hp : pullD (nerveMap (property (p.as 0)).ι) (nerveMap (property (p.as 1)).ι) 2 ≫
      ModuleCat.ofHom (mixedImage a).mkQ=0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (Submodule.Quotient.mk_eq_zero (mixedImage a)).mpr (fiber_value_mem a (p.as 0) (p.as 1) z)
  change SSet.homologyMap _ Z 2 ≫ (pullD _ _ 2 ≫ ModuleCat.ofHom (mixedImage a).mkQ)=_
  erw [hp,comp_zero]
end SimpleAmenable.PolygonTracks

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero_oai := @OAI.SimpleAmenable.PolygonTracks.binaryD_quotient_zero_oai
