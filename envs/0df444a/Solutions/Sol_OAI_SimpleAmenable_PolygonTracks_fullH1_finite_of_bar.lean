-- Prove2me | solution 1 for OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:06:22.502215+00:00
-- url     : https://prove2.me/submissions/63175323-a0f1-4c3b-bc27-97526e5a570d

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

namespace FixedStageReturn

lemma stage_ι_isIso {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    IsIso (colimit.ι F m) := by
  exact (_root_.OAI.CategoryTheory.Functor.isEventuallyConstantFrom_of_succ F N h).isIso_ι_of_isColimit'
    (colimit.isColimit F) m (homOfLE hm)

lemma finite_stage_iff_colimit {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    Module.Finite R (F.obj m) ↔ Module.Finite R (colimit F : ModuleCat R) := by
  have := stage_ι_isIso F N m h hm
  constructor
  · intro hfin
    exact Module.Finite.of_surjective (colimit.ι F m).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · intro hfin
    exact Module.Finite.of_surjective (inv (colimit.ι F m)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end FixedStageReturn

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CofinalPowers
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace CofinalPowers

variable {P:Type} [CommMonoid P]
lemma finite_colimit_iff {R:Type} [Ring R] (x:P) (hx:∀p:P,∃q n,p*q=x^n)
    (F:ActionCategory P P ⥤ ModuleCat R) (N n:ℕ) (hn:N≤n)
    (hf : ∀ m : ℕ, N ≤ m → IsIso (F.map ((sequence x).map (homOfLE (Nat.le_succ m))))) :
    Module.Finite R (F.obj ((sequence x).obj n)) ↔ Module.Finite R (colimit F:ModuleCat R) := by
  exact (FixedStageReturn.finite_stage_iff_colimit (sequence x ⋙ F) N n hf hn).trans
    (Module.Finite.equiv_iff (colimitIso x hx F).toLinearEquiv)
end CofinalPowers

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

lemma finite_of_ker_le [IsNoetherianRing R] (f : A →ₗ[R] B) (g : A →ₗ[R] E)
    (hf : Function.Surjective f) (hker : LinearMap.ker g ≤ LinearMap.ker f)
    [Module.Finite R E] : Module.Finite R B := by
  have : Module.Finite R (LinearMap.range g) :=
    Module.Finite.of_injective (LinearMap.range g).subtype Subtype.val_injective
  have : Module.Finite R (A ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  let φ := (LinearMap.ker g).liftQ f hker
  exact Module.Finite.of_surjective φ (by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨(LinearMap.ker g).mkQ a,rfl⟩)

end FilteredFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Boundary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma finite_E₂ [IsNoetherianRing R] (p q : ℕ)
    [Module.Finite R (ConcreteHomology.H (row K q) p)] :
    Module.Finite R ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply FilteredFiniteness.finite_of_ker_le
    (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
      ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).mkQ (lead K p q)
    (Submodule.mkQ_surjective _)
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (lead_zero_boundary K p q x hx)

end E2Leading

end

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace TrivialHomology
variable (G : Type) [Group G]
lemma abelianization_fg [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] :
    Group.FG (Abelianization G) := by
  let e : groupHomology (Rep.trivial ℤ G ℤ) 1 ≃ₗ[ℤ] Additive (Abelianization G) :=
    (abelianizationEquiv G).toIntLinearEquiv
  have : Module.Finite ℤ (Additive (Abelianization G)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have : AddGroup.FG (Additive (Abelianization G)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact GroupFG.iff_add_fg.mpr inferInstance

end TrivialHomology

end SimpleAmenable

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularTotalDifferential
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace FilteredEdge
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
namespace Data
variable (K : Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ)
omit [IsNoetherianRing R] in
lemma tower_mono : Monotone (K.tower p) := by
  intro k l hkl y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val, K.monoA hkl x.property.1,x.property.2⟩,rfl⟩
omit [IsNoetherianRing R] in
lemma tower_start : K.tower p (p+1)=⊥ := by
  apply le_antisymm _ bot_le
  rintro y ⟨x,rfl⟩
  apply (Submodule.mem_bot R).mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change K.d x.val∈K.current.B₂ p
  exact (show (K.FA (p+1)).map K.d ⊓ K.FB p ≤ K.current.B₂ p from le_sup_right)
    ⟨⟨x.val,x.property.1,rfl⟩,x.property.2⟩
omit [IsNoetherianRing R] in
lemma lower_of_leading_zero (k : ℤ) (hk : p≤k-2) (x : K.inputs p k)
    (hx : K.inputLeading p k hk x=0) :
    K.boundaryMap p k x∈K.tower p (k-1) := by
  have hx' : x.val∈K.previous.B₂ k := (Submodule.Quotient.mk_eq_zero ((K.previous.B₂ k).comap (K.previous.Z₂ k).subtype)).mp hx
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx'
  obtain ⟨w,hw,hwz⟩ := hz.1
  have hd : K.d z = 0 := by
    rw [←hwz]
    exact congrArg (fun f : D →ₗ[R] B => f w) K.ds
  have hxy : K.d y=K.d x.val := by
    rw [←hyz,map_add,hd,add_zero]
  refine ⟨⟨y,hy.1,?_⟩,?_⟩
  · change K.d y∈K.FB p
    rw [hxy]; exact x.property.2
  · change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    exact hxy
lemma finite_tower_step (k : ℤ) (hk : p≤k-2)
    [Module.Finite R (K.tower p (k-1))]
    [Module.Finite R (K.previous.E₂ k)] : Module.Finite R (K.tower p k) := by
  let S : Submodule R (K.tower p k) := (K.tower p (k-1)).submoduleOf (K.tower p k)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.tower_mono p (by omega : k-1≤k))).symm
  let f : K.inputs p k →ₗ[R] K.tower p k ⧸ S :=
    S.mkQ.comp (K.boundaryMap p k).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hker : LinearMap.ker (K.inputLeading p k hk) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_leading_zero p k hk x hx
  have : Module.Finite R (K.tower p k ⧸ S) :=
    finite_of_ker_le f (K.inputLeading p k hk) hf hker
  exact Module.Finite.of_submodule_quotient S
end Data
end FilteredEdge

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredEdgeReturn
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace FilteredEdge.Data
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
variable (K : FilteredEdge.Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ) (hp : K.FC (p-2)=⊥)
omit [IsNoetherianRing R] in
lemma edge_kernel_le_tower (N : ℤ) (hN : K.FA N=⊤) :
    LinearMap.ker (K.edgeMap p hp) ≤ K.tower p N := by
  intro z hz
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    ((K.current.B₂ p).comap (K.current.Z₂ p).subtype) z
  have hx : K.edgeLift p hp x=0 := hz
  have hx' : K.current.π (K.edgeCycles p hp x)∈K.current.filtration (p-1) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y,hy⟩ := hx'
  have hxy : K.current.π (K.edgeCycles p hp x-y.val)=0 := by
    rw [map_sub,show K.current.π y.val=K.current.π (K.edgeCycles p hp x) from hy,sub_self]
  obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hxy
  have hav : K.d a=x.val-y.val.val := congrArg Subtype.val ha
  have had : K.d a∈K.FB p := by
    rw [hav]
    exact (K.FB p).sub_mem x.property.1 (K.monoB (by omega) y.property)
  refine ⟨⟨a,by rw [hN]; trivial,had⟩,?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change K.d a-x.val∈K.current.B₂ p
  rw [hav,sub_sub_cancel_left]
  apply Submodule.mem_sup_left
  refine ⟨(K.FB (p-1)).neg_mem y.property,?_⟩
  change K.e (-y.val.val)∈K.FC (p-2)
  have hey : K.e y.val.val=0 := y.val.property
  rw [map_neg,hey,neg_zero]
  exact Submodule.zero_mem _
include hp in
lemma finite_edge (N : ℤ) (hN : K.FA N=⊤)
    [Module.Finite R K.current.H] [Module.Finite R (K.tower p N)] :
    Module.Finite R (K.current.E₂ p) := by
  let f := K.edgeMap p hp
  have : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_injective (Submodule.inclusion (K.edge_kernel_le_tower p hp N hN))
      (Submodule.inclusion_injective _)
  have : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_injective (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite R (K.current.E₂ p ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)
lemma finite_tower (r : ℕ)
    (hfinite : ∀i:ℕ, i < r → Module.Finite R (K.previous.E₂ (p+i+2))) :
    Module.Finite R (K.tower p (p+r+1)) := by
  induction r with
  | zero => rw [Nat.cast_zero,add_zero,K.tower_start]; infer_instance
  | succ r ih =>
    have := ih (fun i hi => hfinite i (by omega))
    have := hfinite r (by omega)
    have he : p+(r+1:ℕ)+1=p+r+2 := by push_cast; omega
    rw [he]
    have : Module.Finite R (K.tower p (p+r+2-1)) := by
      rw [show p+(r:ℤ)+2-1=p+r+1 by ring]
      exact ih (fun i hi => hfinite i (by omega))
    exact K.finite_tower_step p (p+r+2) (by omega)
end FilteredEdge.Data

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma lift_first_cycle (q : ℕ) (y : ConcreteHomology.Cycles (K.X 1) q)
    (z : (K.X 0).X (q+1)) (hz : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val) :
    ∃ x : (filteredData K (1+q)).Z₂ 2, projection K 1 q (1+q) x.val=y.val := by
  have hw : (K.total c).d (0+q+1) (0+q) (lift K 0 q y.val (-z))=0 := by
    apply (Submodule.mem_bot R).mp
    rw [←filtration_zero K (0+q)]
    apply lower_filtration K 0 q (d_lift_mem K 0 q y (-z))
    rw [d_lift_top,map_neg,hz,add_neg_cancel]
  have aux : ∃ x : (filteredData K (0+q+1)).Z₂ 2,
      projection K 1 q (0+q+1) x.val=y.val := by
    refine ⟨⟨lift K 0 q y.val (-z),lift_mem K 0 q y.val (-z),?_⟩,lift_left K 0 q y.val (-z)⟩
    change (K.total c).d (0+q+1) (0+q+1-1) (lift K 0 q y.val (-z))∈filtration K (0+q+1-1) (2-2)
    rw [Nat.add_sub_cancel,hw]
    exact Submodule.zero_mem _
  rw [show 1+q=0+q+1 by omega]
  exact aux
lemma first_lead_surjective (q : ℕ) : Function.Surjective (lead K 1 q) := by
  intro v
  obtain ⟨w,rfl⟩ := ConcreteHomology.π_surjective (row K q) 1 v
  obtain ⟨y,hy⟩ := ConcreteHomology.π_surjective (K.X 1) q w.val
  have hdy : ConcreteHomology.π (K.X 0) q
      (ConcreteHomology.cyclesMap (K.d 1 0) q y)=0 := by
    rw [←ConcreteHomology.map_π,hy]
    exact w.property
  obtain ⟨z,hz⟩ := (ConcreteHomology.π_eq_zero _ _ _).mp hdy
  have hzv : (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val := by
    have h := congrArg Subtype.val hz
    change (K.X 0).d (q+1) q z=(K.d 1 0).f q y.val at h
    exact h
  obtain ⟨x,hx⟩ := lift_first_cycle K q y z hzv
  refine ⟨x,?_⟩
  change ConcreteHomology.π (row K q) 1 (topRowCycle K 1 q x)=_
  congr 1
  apply Subtype.ext
  change ConcreteHomology.π (K.X 1) q (topCycle K 1 q x)=w.val
  rw [show topCycle K 1 q x=y by apply Subtype.ext; exact hx,hy]
end E2Leading

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Descend
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma first_descendedLead_surjective (q : ℕ) : Function.Surjective (descendedLead K 1 q) := by
  intro y
  obtain ⟨x,hx⟩ := first_lead_surjective K q y
  exact ⟨Submodule.Quotient.mk x,hx⟩
end E2Leading

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ)
    [Module.Finite R (ConcreteHomology.H (K.total c) (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R (ConcreteHomology.H (row K r) p)) :
    Module.Finite R (ConcreteHomology.H (row K q) 1) := by
  let E := edgeData K (1+q)
  have : Module.Finite R E.current.H := ‹Module.Finite R (ConcreteHomology.H (K.total c) (1+q))›
  have : Module.Finite R (E.tower 2 (2+(q:ℤ)+1)) := by
    apply E.finite_tower 2 q
    intro i hi
    have hpq : (i+3)+(q-1-i)=1+q+1 := by omega
    have := hf (i+3) (q-1-i) (by omega) (by omega)
    have ht := finite_E₂ K (i+3) (q-1-i)
    rw [hpq] at ht
    change Module.Finite R ((filteredData K (1+q+1)).E₂ (2+(i:ℤ)+2))
    rw [show ((i+3:ℕ):ℤ)+1=2+(i:ℤ)+2 by omega] at ht
    exact ht
  have hzero : E.FC (2-2)=⊥ := filtration_zero K (1+q-1)
  have htop : E.FA (2+(q:ℤ)+1)=⊤ := by
    change filtration K (1+q+1) (2+(q:ℤ)+1)=⊤
    rw [show 2+(q:ℤ)+1=((1+q+1:ℕ):ℤ)+1 by omega]
    exact filtration_top K (1+q+1)
  have : Module.Finite R ((filteredData K (1+q)).E₂ ((1:ℤ)+1)) :=
    E.finite_edge 2 hzero (2+(q:ℤ)+1) htop
  exact Module.Finite.of_surjective (descendedLead K 1 q) (first_descendedLead_surjective K q)
end E2Leading
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma finite_first (q : ℕ) [Module.Finite R ((K.total c).homology (1+q))]
    (hf : ∀ p r, p+r=q+2 → 3≤p → Module.Finite R ((row K r).homology p)) :
    Module.Finite R ((row K q).homology 1) := by
  have : Module.Finite R (ConcreteHomology.H (K.total c) (1+q)) :=
    Module.Finite.equiv (ConcreteHomology.iso (K.total c) (1+q)).toLinearEquiv
  have : Module.Finite R (ConcreteHomology.H (E2Leading.row K q) 1) := by
    apply E2Leading.finite_first K q
    intro p r hpr hp
    have := hf p r hpr hp
    exact Module.Finite.equiv (rowHomologyIso K p r).toLinearEquiv
  exact Module.Finite.equiv (rowHomologyIso K 1 q).symm.toLinearEquiv
end TotalFiniteness

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonCoefficientFinite
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

section NoetherianResolution
open _root_.CategoryTheory CategoryTheory.Limits
universe nr

namespace NoetherianResolution
variable {R : Type nr} [CommRing R] [IsNoetherianRing R]

theorem finite_short_homology (S : ShortComplex (ModuleCat.{nr} R))
    [Module.Finite R S.X₂] : Module.Finite R S.homology := by
  have : Module.Finite R (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    exact Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (LinearMap.range S.moduleCatToCycles).mkQ_surjective
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    S.moduleCatHomologyIso.toLinearEquiv.symm.surjective

theorem finite_homology (C : ChainComplex (ModuleCat.{nr} R) ℕ) (n : ℕ)
    [Module.Finite R (C.X n)] : Module.Finite R (C.homology n) := by
  have : Module.Finite R (C.sc n).X₂ := ‹Module.Finite R (C.X n)›
  exact finite_short_homology (C.sc n)

end NoetherianResolution
end NoetherianResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_NoetherianTor
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
section NoetherianTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe nt

namespace NoetherianResolution
variable {R : Type nt} [CommRing R]

theorem homologyMap_smul {C D : ChainComplex (ModuleCat.{nt} R) ℕ}
    (f : C ⟶ D) (r : R) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n =
      r • HomologicalComplex.homologyMap f n := by
  exact ShortComplex.homologyMap_smul
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) _ n).map f) r

theorem annihilator_homology {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (F : ModuleCat.{nt} R ⥤ ModuleCat.{nt} R)
    [F.Additive] [Functor.Linear R F] (r : R) (hr : ∀ x : M, r • x = 0)
    (n : ℕ) (x : ((F.mapHomologicalComplex _).obj P.complex).homology n) :
    r • x = 0 := by
  have h := (F.mapHomotopy (annihilatorHomotopy P r hr)).homologyMap_eq n
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero,
    homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

variable [IsNoetherianRing R]

theorem finite_tensor_resolution_homology (L M : FGModuleCat.{nt} R) (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).homology n) := by
  have : Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).X n) :=
    Module.Finite.tensorProduct R L ((resolution M).complex.X n)
  exact finite_homology _ n

end NoetherianResolution

theorem module_finite_int_of_augmentation {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ε : R →+* ℤ) (h : ∀ (r : R) (x : M), r • x = ε r • x) :
    Module.Finite ℤ M := by
  obtain ⟨s,hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [h]; exact Submodule.smul_mem _ _ hx

end NoetherianTor

section AugmentationTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace NoetherianResolution
variable {R : Type} [CommRing R] [IsNoetherianRing R]

instance finite_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite R ((augmentationComplex ε L).homology n) :=
  finite_tensor_resolution_homology L (FGModuleCat.of R (augmentationModule ε)) n

theorem augmentation_homology_smul (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ)
    (r : R) (x : (augmentationComplex ε L).homology n) :
    r • x = ε r • x := by
  have h0 : ∀ z : augmentationModule ε, (r - (ε r : R)) • z = 0 := by
    intro z
    change ε (r - (ε r : R)) • z = 0
    simp only [map_sub, map_intCast, Int.cast_id, sub_self, zero_smul]
  have h := annihilator_homology (augmentationResolution ε)
    ((tensoringLeft (ModuleCat R)).obj L.obj) (r - (ε r : R)) h0 n x
  have h' : (r - (ε r : R)) • x = 0 := h
  rw [sub_smul, sub_eq_zero] at h'
  simpa only [Int.cast_smul_eq_zsmul] using h'

theorem finite_int_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ ((augmentationComplex ε L).homology n) :=
  module_finite_int_of_augmentation ε (augmentation_homology_smul ε L n)

end NoetherianResolution
end AugmentationTor

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RingGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section RingGroupHomology

open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

variable [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology_inverse (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ (groupHomology (inverseRep L.obj) n) := by
  classical
  let C := NoetherianResolution.augmentationComplex (augmentation (G := G)) L
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let := NoetherianResolution.finite_int_augmentation_homology augmentation L n
  let e0 : ModuleCat.of ℤ (C.homology n) ≅ F.obj (C.homology n) := intRestrictionIso _
  have : Module.Finite ℤ (F.obj (C.homology n)) :=
    Module.Finite.of_surjective e0.hom.hom e0.toLinearEquiv.surjective
  let e1 : ((F.mapHomologicalComplex _).obj C).homology n ≅
      F.obj (C.homology n) := (C.sc n).mapHomologyIso F
  have : Module.Finite ℤ (((F.mapHomologicalComplex _).obj C).homology n) :=
    Module.Finite.of_surjective e1.inv.hom e1.toLinearEquiv.symm.surjective
  let e2 := HomologicalComplex.homologyMapIso (complexIso L) n
  have : Module.Finite ℤ (((groupResolution (G := G)).complex.coinvariantsTensorObj
      (inverseRep L.obj)).homology n) :=
    Module.Finite.of_surjective e2.inv.hom e2.toLinearEquiv.symm.surjective
  let e3 := groupHomologyIso (inverseRep L.obj) n (groupResolution (G := G))
  exact Module.Finite.of_surjective e3.inv.hom e3.toLinearEquiv.symm.surjective

end RingCoinvariants
end RingGroupHomology

section FiniteAbelianHomology

open _root_.CategoryTheory
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G] [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology (A : Rep ℤ G)
    [Module.Finite (MonoidAlgebra ℤ G) A.ρ.asModule] (n : ℕ) :
    Module.Finite ℤ (groupHomology A n) := by
  let L := FGModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule
  have := finite_groupHomology_inverse L n
  let e := inverseHomologyIso A n
  exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective

end RingCoinvariants
end FiniteAbelianHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AbelianHomologyFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace AbelianHomologyFinite
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable (G:Type) [CommGroup G]
lemma fg [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] : Group.FG G := by
  have :=TrivialHomology.abelianization_fg G
  exact Group.fg_of_surjective (f:=(Abelianization.equivOfComm (H:=G)).symm.toMonoidHom)
    (Abelianization.equivOfComm (H:=G)).symm.surjective
lemma finite (n:ℕ) [Group.FG G] : Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) n) := by
  have : Algebra.FiniteType ℤ (MonoidAlgebra ℤ G) := MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  have : IsNoetherianRing (MonoidAlgebra ℤ G) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Module.Finite ℤ (Rep.trivial ℤ G ℤ).ρ.asModule := by
    exact Module.Finite.equiv (Representation.trivial ℤ G ℤ).asModuleEquiv.symm
  have : Module.Finite (MonoidAlgebra ℤ G) (Rep.trivial ℤ G ℤ).ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  exact RingCoinvariants.finite_groupHomology _ n
end AbelianHomologyFinite
namespace TranslationNerve
open FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
lemma homology_finite_of_one (n:ℕ) [Module.Finite ℤ ((nerve (SingleObj P)).homology Z 1 : A)] :
    Module.Finite ℤ ((nerve (SingleObj P)).homology Z n : A) := by
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ (TranslationFiltered.Q P) ℤ) 1) :=
    Module.Finite.equiv (completionHomologyIso P 1).toLinearEquiv
  have :=AbelianHomologyFinite.fg (TranslationFiltered.Q P)
  have :=AbelianHomologyFinite.finite (TranslationFiltered.Q P) n
  exact Module.Finite.equiv (completionHomologyIso P n).symm.toLinearEquiv
end TranslationNerve

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarComponentsFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace IntervalBar.Diagram
open FreeChains SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma first_row_finite (q:ℕ)
    [Module.Finite ℤ ((bar (C:=C)).homology Z (1+q) : A)]
    (hf:∀p r,p+r=q+2 → 3≤p → Module.Finite ℤ ((homologyRow (C:=C) r).homology p)) :
    Module.Finite ℤ ((homologyRow (C:=C) q).homology 1) := by
  let X := simplicial (C:=C) ⋙ nerveFunctor
  let K := EilenbergZilber.twoComplex (uncurry X)
  have : Module.Finite ℤ ((K.total c).homology (1+q)) := by
    let e : ((bar (C:=C)).homology Z (1+q) : A) ≅ (K.total c).homology (1+q) :=
      EilenbergZilber.homologyIsoN (uncurry X) (1+q)
    exact Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite ℤ ((TotalFiniteness.row K q).homology 1) := by
    apply TotalFiniteness.finite_first K q
    intro p r hpr hp
    have : Module.Finite ℤ ((AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z r)).homology p) := hf p r hpr hp
    exact Module.Finite.equiv (homologyRowHomologyIso X p r).symm.toLinearEquiv
  exact Module.Finite.equiv (homologyRowHomologyIso X 1 q).toLinearEquiv
lemma component_homology_finite (n:ℕ)
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)] :
    Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z n : A) := by
  have : Module.Finite ℤ ((homologyRow (C:=C) 0).homology 1) :=
    first_row_finite 0 (by intro p r hpr hp; omega)
  have : Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z 1 : A) := by
    let e : (homologyRow (C:=C) 0).homology 1 ≅ (nerve (SingleObj (Skeleton C))).homology Z 1 :=
      (homologyFunctor A c 1).mapIso (componentRowChainIso (C:=C) ≪≫ (complexIso _).symm)
    exact Module.Finite.equiv e.toLinearEquiv
  exact TranslationNerve.homology_finite_of_one _ n
lemma first_row_one_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2 : A)] :
    Module.Finite ℤ ((homologyRow (C:=C) 1).homology 1) := by
  apply first_row_finite 1
  intro p r hpr hp
  have hr:r=0:=by omega
  subst r
  have:=component_homology_finite (C:=C) p
  let e : ((nerve (SingleObj (Skeleton C))).homology Z p : A) ≅ (homologyRow (C:=C) 0).homology p :=
    (homologyFunctor A c p).mapIso ((complexIso _) ≪≫ (componentRowChainIso (C:=C)).symm)
  exact Module.Finite.equiv e.toLinearEquiv
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarStableH1
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite AlgebraicTopology
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma stableH1_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2 : A)] :
    Module.Finite ℤ (ComponentStable.object (C:=C) 1 : A) := by
  have :=first_row_one_finite (C:=C)
  exact Module.Finite.of_surjective (stableOneπ (C:=C)).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end MarkedH1

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
lemma finite_fullH1_iff_stable (a m:ℕ) (hm : 32 ≤ m) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) ↔
      Module.Finite ℤ (ComponentStable.object (C:=PolygonObject a) 1 : A) := by
  refine (Module.Finite.equiv_iff (standardHomologyIso a m 1).toLinearEquiv).trans ?_
  apply CofinalPowers.finite_colimit_iff (componentGenerator a) (componentGenerator_cofinal a)
    (homologyDiagram 1) 32 m hm
  intro n hn
  rw [component_sequence_succ]
  have successorIso := successor_H1_isIso a n hn
  exact component_successor_isIso a n 1
lemma fullH1_finite_of_bar_oai (a m:ℕ) (hm : 32 ≤ m)
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 1 : A)]
    [Module.Finite ℤ ((IntervalBar.Diagram.bar (C:=PolygonObject a)).homology Z 2 : A)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1) :=
  (finite_fullH1_iff_stable a m hm).mpr (MarkedH1.stableH1_finite (C:=PolygonObject a))
end SimpleAmenable.PolygonTracks

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar_oai := @OAI.SimpleAmenable.PolygonTracks.fullH1_finite_of_bar_oai
