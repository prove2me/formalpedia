-- Prove2me | solution 1 for OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:05:17.092725+00:00
-- url     : https://prove2.me/submissions/0dc81127-66c7-4deb-bc75-32fd9bd76ecb

import Mathlib
import Definitions.Def_OAIQ65Sa020

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FreshEvenBank
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
section FreshEvenBank

theorem even_move_embedding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : n + 2 ≤ Nat.card α) (s t : Fin n ↪ α) :
    ∃ σ : alternatingGroup α, ∀ i, σ.val (s i) = t i := by
  let :=  alternatingGroup.isMultiplyPretransitive α
  let : MulAction.IsMultiplyPretransitive (alternatingGroup α) α n :=
    MulAction.isMultiplyPretransitive_of_le (by omega : n ≤ Nat.card α - 2)
      (Nat.sub_le _ _)
  obtain ⟨σ,hσ⟩ := MulAction.exists_smul_eq (alternatingGroup α) s t
  exact ⟨σ,fun i => congrArg (fun e : Fin n ↪ α => e i) hσ⟩

end FreshEvenBank

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralTransgressionFinite
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

section IntegralHomologyConjugation
open Classical _root_.CategoryTheory Finsupp groupHomology
namespace IntegralHomology

variable {E F : Type} [Group E] [Group F]

lemma boundary2_single (x y : E) (n : ℤ) :
    d₂₁ (coefficients E) (single (x,y) n)=single y n-single (x*y) n+single x n := by
  rw [d₂₁_single]
  rfl

lemma boundary3_single (x y z : E) (n : ℤ) :
    d₃₂ (coefficients E) (single (x,y,z) n)=
      single (y,z) n-single (x*y,z) n+single (x,y*z) n-single (x,y) n := by
  rw [d₃₂_single]
  rfl

theorem prism_identity (c : E) :
    (d₃₂ (coefficients E)).hom.comp (prism2 c) +
      (prism1 c).comp (d₂₁ (coefficients E)).hom =
        LinearMap.id - mapC2 (MulAut.conj c).toMonoidHom := by
  apply Finsupp.lhom_ext
  intro xy n
  rcases xy with ⟨x,y⟩
  change d₃₂ (coefficients E) (prism2 c (single (x,y) n)) +
    prism1 c (d₂₁ (coefficients E) (single (x,y) n)) =
    single (x,y) n-mapC2 (MulAut.conj c).toMonoidHom (single (x,y) n)
  rw [prism2_single, map_add, map_sub, boundary3_single, boundary3_single,
    boundary3_single, boundary2_single, map_add, map_sub, prism1_single,
    prism1_single, prism1_single, mapC2_single]
  simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,mul_assoc,
    inv_mul_cancel_left,inv_mul_cancel,mul_one]
  abel

end IntegralHomology
end IntegralHomologyConjugation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_IntegralHomologyFunctorial
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
section IntegralHomologyFunctorial
open Classical _root_.CategoryTheory Finsupp groupHomology
namespace IntegralHomology
variable {E F G : Type} [Group E] [Group F] [Group G]

lemma chainsMap2_eq (f : E →* F) :
    (chainsMap₂ f (coefficientMap f)).hom=mapC2 f := by
  apply Finsupp.lhom_ext
  intro xy n
  simp [chainsMap₂,coefficientMap,mapC2]

lemma cyclesMap2_val (f : E →* F) (x : cycles₂ (coefficients E)) :
    (mapCycles₂ f (coefficientMap f) x).val=mapC2 f x.val := by
  rw [coe_mapCycles₂]
  exact LinearMap.congr_fun (chainsMap2_eq f) x.val

theorem mapH2_inner (c : E) : mapH2 (MulAut.conj c).toMonoidHom=LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using H2_induction_on with
  | h x =>
    change groupHomology.map (MulAut.conj c).toMonoidHom _ 2 (H2π (coefficients E) x)=
      H2π (coefficients E) x
    rw [H2π_comp_map_apply]
    apply (H2π_eq_iff _ _).mpr
    change ∃y, d₃₂ (coefficients E) y=
      (mapCycles₂ (MulAut.conj c).toMonoidHom (coefficientMap _) x).val-x.val
    rw [cyclesMap2_val]
    refine ⟨-prism2 c x.val,?_⟩
    have ht := LinearMap.congr_fun (prism_identity c) x.val
    change d₃₂ (coefficients E) (prism2 c x.val) + prism1 c (d₂₁ (coefficients E) x.val) =
      x.val-mapC2 (MulAut.conj c).toMonoidHom x.val at ht
    have hx : d₂₁ (coefficients E) x.val=0 := x.property
    rw [hx,map_zero,add_zero] at ht
    rw [map_neg,ht]
    abel

theorem mapH2_comp (f : E →* F) (g : F →* G) :
    mapH2 (g.comp f)=(mapH2 g).comp (mapH2 f) := by
  have he : coefficientMap (g.comp f)=coefficientMap f ≫ (Rep.resFunctor f).map (coefficientMap g) := by
    apply Rep.hom_ext
    ext
    rfl
  unfold mapH2
  rw [he,groupHomology.map_comp]
  rfl

theorem mapH2_conjugate (c : F) (f : E →* F) :
    mapH2 ((MulAut.conj c).toMonoidHom.comp f)=mapH2 f := by
  rw [mapH2_comp,mapH2_inner,LinearMap.id_comp]

end IntegralHomology
end IntegralHomologyFunctorial

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementAlternating
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPlacementAlternating

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem permHom_mem_alternating (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (hm : 3*n+1 < m)
    {σ : Equiv.Perm (Fin n)} (hσ : σ∈alternatingGroup (Fin n)) :
    permHom f hf σ∈polygonAlternatingGroup a m := by
  let ι : Fin n ↪ Fin m := Fin.castLEEmb (by omega)
  let s : Fin n → PolygonPlacement a m := fun i => standard (ι i)
  have hs : Pairwise (fun i j => Apart (s i) (s j)) :=
    fun _ _ hij => standard_apart (ι.injective.ne hij)
  obtain ⟨g,hg⟩ := configuration_transitive s f hs hf hm
  have hgs (i : Fin n) (x : GenericSquare a) : g.val (ι i,x)=f i x :=
    congrArg (fun e : PolygonPlacement a m => e x) (hg i)
  let slots : Fin n → Fin m × (CutRing×CutRing) := fun i => (ι i,0)
  have hinj : Function.Injective (SlotMap a m ⊤ slots) :=
    slots_injective_of_tracks ⊤ slots ι.injective
  have hslot (i : Fin n) (x : (⊤ : polygonAlgebra a).val) :
      SlotMap a m ⊤ slots (i,x)=(ι i,x.val) := by
    change (ι i,translate a 0 x.val)=(ι i,x.val)
    rw [translate_zero]
  have he : g*slotHom ⊤ slots hinj σ*g⁻¹=permHom f hf σ := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    obtain ⟨q,rfl⟩ := g.val.surjective p
    change g.val (slotPerm ⊤ slots hinj σ (g.val.symm (g.val q)))=perm f hf σ (g.val q)
    rw [g.val.symm_apply_apply]
    by_cases hq : q∈Set.range (SlotMap a m ⊤ slots)
    · obtain ⟨⟨i,x⟩,rfl⟩ := hq
      rw [slotPerm_apply,hslot,hslot,hgs,hgs,perm_apply]
    · rw [slotPerm_apply_of_notMem _ _ _ _ hq]
      symm
      apply perm_fixed
      intro i hmem
      obtain ⟨x,hx⟩ := hmem
      have hp : q=(ι i,x) := g.val.injective (hx.symm.trans (hgs i x).symm)
      exact hq ⟨(i,⟨x,by trivial⟩),(hslot i ⟨x,by trivial⟩).trans hp.symm⟩
  rw [←he]
  exact (polygonAlternatingGroup_normal a m).conj_mem _ (slotHom_alternating_mem _ _ _ hσ) g

end PolygonPlacement
end PolygonPlacementAlternating

section PolygonAlternatingTransitive

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem familyPerm_mem_alternating {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → PolygonPlacement a m) (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hm : 3*Fintype.card ι+1 < m) {σ : Equiv.Perm ι}
    (hσ : σ∈alternatingGroup ι) : familyPerm f hf σ∈polygonAlternatingGroup a m := by
  apply permHom_mem_alternating _ _ hm
  change Equiv.Perm.sign (((Fintype.equivFin ι).symm.trans σ).trans (Fintype.equivFin ι))=1
  rw [Equiv.Perm.sign_symm_trans_trans]
  exact hσ

theorem alternating_move_to_bank (f : Fin n → PolygonPlacement a m)
    (w : Fin (n+2) → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hw : Pairwise (fun i j => Apart (w i) (w j)))
    (hfw : ∀i j,Apart (f i) (w j)) (hm : 6*n+7 < m) :
    ∃h : polygonAlternatingGroup a m,∀i x,h.val.val (f i x)=w (i.castAdd 2) x := by
  let e : Fin n ⊕ Fin (n+2) → PolygonPlacement a m := Sum.elim f w
  have he : Pairwise (fun i j => Apart (e i) (e j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hf (fun hh => hij (congrArg Sum.inl hh))
      | inr j => exact hfw i j
    | inr i =>
      cases j with
      | inl j => exact (hfw j i).symm
      | inr j => exact hw (fun hh => hij (congrArg Sum.inr hh))
  let s : Fin n ↪ Fin n ⊕ Fin (n+2) := ⟨Sum.inl,Sum.inl_injective⟩
  let t : Fin n ↪ Fin n ⊕ Fin (n+2) :=
    ⟨fun i => Sum.inr (i.castAdd 2),by
      intro i j h
      have hc : i.castAdd 2=j.castAdd 2 := Sum.inr_injective h
      have hv := congrArg (fun x : Fin (n+2) => x.val) hc
      exact Fin.ext hv⟩
  obtain ⟨σ,hσ⟩ := even_move_embedding (s:=s) (t:=t) (by simp [Nat.card_eq_fintype_card])
  have hb : 3*Fintype.card (Fin n ⊕ Fin (n+2))+1 < m := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  refine ⟨⟨familyPerm e he σ.val,familyPerm_mem_alternating e he hb σ.property⟩,?_⟩
  intro i x
  have hh := familyPerm_apply e he σ.val (s i) x
  rw [hσ] at hh
  exact hh

theorem alternating_configuration_transitive (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 6*n+7 < m) :
    ∃h : polygonAlternatingGroup a m,∀i,h.val • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S (n+2) (by omega)
  have hfw (i : Fin n) (j : Fin (n+2)) : Apart (f i) (w j) :=
    (hws j (f i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).symm
  have hgw (i : Fin n) (j : Fin (n+2)) : Apart (g i) (w j) :=
    (hws j (g i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).symm
  obtain ⟨u,hu⟩ := alternating_move_to_bank f w hf hw hfw hm
  obtain ⟨v,hv⟩ := alternating_move_to_bank g w hg hw hgw hm
  refine ⟨v⁻¹*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val.val.symm (u.val.val (f i x))=g i x
  rw [hu]
  exact v.val.val.symm_apply_eq.mpr (hv i x).symm

end PolygonPlacement
end PolygonAlternatingTransitive

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonAlternatingStabilization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAlternatingStabilization
open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

theorem stabilizeAlternating_injective : Function.Injective (stabilizeAlternating a k n) := by
  intro g h he
  apply Subtype.ext
  exact stabilize_injective (congrArg Subtype.val he)

theorem exists_alternating_agrees_right (f : polygonFullGroup a (k+n)) (hm : 6*n+7<k+n) :
    ∃c : polygonAlternatingGroup a (k+n),∀x : TrackPoint a n,
      c.val.val (rightIncl a k n x)=f.val (rightIncl a k n x) := by
  let e : Fin n → PolygonPlacement a (k+n) := fun i => PolygonPlacement.standard (i.natAdd k)
  have he : Pairwise (fun i j => PolygonPlacement.Apart (e i) (e j)) := by
    intro i j hij
    exact PolygonPlacement.standard_apart (fun h => hij (Fin.ext (Nat.add_left_cancel
      (congrArg Fin.val h))))
  have hf : Pairwise (fun i j => PolygonPlacement.Apart (f • e i) (f • e j)) := by
    intro i j hij
    exact (PolygonPlacement.apart_smul_iff f _ _).mpr (he hij)
  obtain ⟨c,hc⟩ := PolygonPlacement.alternating_configuration_transitive e (fun i => f • e i) he hf hm
  refine ⟨c,fun x => ?_⟩
  exact congrArg (fun z : PolygonPlacement a (k+n) => z x.2) (hc x.1)

end PolygonTracks
end PolygonAlternatingStabilization

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BoundedHomologyEdge
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory CategoryTheory.Limits

namespace BoundedHomologyEdge

universe u
variable {k G : Type u} [CommRing k] [Group G]

section TwoKernels
variable {Z₁ Z₂ C₀ C₁ C₂ C₃ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (e : C₃ ⟶ Z₂) [Epi e]

include h₂

include h₁

lemma H2_epi_of_isZero [IsIso (Hmap 0 (e ≫ i₂))]
    (hperfect : IsZero (groupHomology C₂ 1)) : Epi (Hmap 2 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  have hz : IsZero (groupHomology Z₁ 1) := IsZero.of_epi (Hmap 1 p₂) hperfect
  exact epi_Hmap_succ_of_isZero h₁ 1 hz

end TwoKernels

section KernelWindow

variable {C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃) (d₅ : C₅ ⟶ C₄)
  (w₂ : d₂ ≫ d₁ = 0) (w₃ : d₃ ≫ d₂ = 0) (w₄ : d₄ ≫ d₃ = 0) (w₅ : d₅ ≫ d₄ = 0)

lemma chain_H2_epi [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    [IsIso (Hmap 0 d₃)] (hz : IsZero (groupHomology C₂ 1)) : Epi (Hmap 2 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  exact H2_epi_of_isZero (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (lift₃ d₁ d₂ d₃ w₂ w₃) hz

end KernelWindow

end BoundedHomologyEdge

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullGroupStability
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TrivialHomology

attribute [local instance 1200] Rep.hV2
variable {G H : Type} [Group G] [Group H]

lemma H1_isZero_of_perfect [Group.IsPerfect G] :
    IsZero (groupHomology.H1 (Rep.trivial ℤ G ℤ)) := by
  have : Group.IsPerfect (Abelianization G) := Group.IsPerfect.ofSurjective
    (f:=Abelianization.of) (QuotientGroup.mk'_surjective (_root_.commutator G))
  have : Subsingleton (Abelianization G) := inferInstance
  have : Subsingleton (groupHomology.H1 (Rep.trivial ℤ G ℤ)) :=
    (abelianizationEquiv G).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end SimpleAmenable.TrivialHomology

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PermutationAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction

attribute [local instance 1200] Rep.hV2
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

lemma augmentation_natural (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) :
    equivariantMap f hf ≫ augmentation G Y=augmentation G X := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro x z
  change (augmentation G Y).hom ((equivariantMap f hf).hom (single x z))=
    (augmentation G X).hom (single x z)
  rw [equivariantMap_single, augmentation_single, augmentation_single]
lemma augmentation_pointMap (x : X) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q ≫
      (groupHomology.functor ℤ G q).map (augmentation G X) =
    TrivialHomology.map (MulAction.stabilizer G x).subtype q := by
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (augmentation G X).hom (single x z)=z
    exact augmentation_single x z
lemma isIso_H0_augmentation (x : X) (ht : ∀y:X,∃g:G,g • x=y) :
    IsIso ((groupHomology.functor ℤ G 0).map (augmentation G X)) := by
  have pointIso := isIso_map_pointMap x ht 0
  have trivialIso := isIso_map_trivial_H0 (MulAction.stabilizer G x).subtype
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso trivialIso
    (augmentation_pointMap x 0)

lemma map_equivariant_H0_eq (f₀ f₁ : X → Y)
    (h₀ : ∀g : G,∀x,f₀ (g • x)=g • f₀ x)
    (h₁ : ∀g : G,∀x,f₁ (g • x)=g • f₁ x)
    (y : Y) (ht : ∀z:Y,∃g:G,g • y=z) :
    (groupHomology.functor ℤ G 0).map (equivariantMap f₀ h₀)=
      (groupHomology.functor ℤ G 0).map (equivariantMap f₁ h₁) := by
  have := isIso_H0_augmentation y ht
  apply (cancel_mono ((groupHomology.functor ℤ G 0).map (augmentation G Y))).1
  rw [← Functor.map_comp, ← Functor.map_comp, augmentation_natural, augmentation_natural]
end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_AlternatingStability
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2
namespace PolygonPlacement.Configuration
variable {a m p n : ℕ}

lemma alternatingStabilizerEquiv_subtype (a p n : ℕ) (hn : 32 ≤ n) :
    (MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)).subtype.comp
      (alternatingStabilizerEquiv a p n hn).toMonoidHom=PolygonTracks.stabilizeAlternating a p n := rfl

lemma alternatingStabilizer_perfect (a p n : ℕ) (hn : 32 ≤ n) :
    Group.IsPerfect (MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)) := by
  have := polygonAlternatingGroup_perfect a n (by omega)
  exact Group.IsPerfect.ofSurjective (f:=(alternatingStabilizerEquiv a p n hn).toMonoidHom)
    (alternatingStabilizerEquiv a p n hn).surjective

lemma altBoundary_exact (a m p : ℕ) (hm : 33 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (altBoundary a m (p+1)) (altBoundary a m p) (altBoundary_square a m p)).Exact := by
  exact (Rep.res_map_exact (polygonAlternatingGroup a m).subtype
    (ShortComplex.mk (boundary a m (p+1)) (boundary a m p) (boundary_square a m p))).mpr
      (boundary_exact a m p hm hp)

lemma altBoundary_zero_epi (a m : ℕ) (hm : 0 < m) : Epi (altBoundary a m 0) := by
  rw [Rep.epi_iff_surjective]
  exact (Rep.epi_iff_surjective (boundary a m 0)).mp (boundary_zero_epi a m hm)

lemma altFace_H0_eq (a m p : ℕ) (hm : 3*p+1 < m) (i j : Fin (p+1)) :
    (groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p i)=
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p j) := by
  let f := standardLE a m p (by omega : p ≤ m)
  exact TransitiveInduction.map_equivariant_H0_eq (G:=polygonAlternatingGroup a m)
    (face i) (face j) (fun g x => face_smul i g.val x) (fun g x => face_smul j g.val x)
    f (fun g => alternating_transitive f g hm)

lemma altFace_H0_isIso (a m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p i)) := by
  let f := standardLE a m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (G:=polygonAlternatingGroup a m)
    (face i) (fun g x => face_smul i g.val x) f
      (fun g => alternating_transitive f g hm) (fun g => alternating_transitive _ g (by omega))

lemma altBoundary_two_H0_isIso (a m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altBoundary a m 2)) := by
  have he : altBoundary a m 2=altFaceHom a m 2 0-altFaceHom a m 2 1+altFaceHom a m 2 2 := by
    change (Rep.resFunctor _).map (boundary a m 2)=_
    rw [boundary_three, Functor.map_add, Functor.map_sub]
  rw [he, Functor.map_add, Functor.map_sub,
    altFace_H0_eq a m 2 (by omega) 1 0, altFace_H0_eq a m 2 (by omega) 2 0,
    sub_self,zero_add]
  exact altFace_H0_isIso a m 2 hm 0

lemma altColumn_H1_isZero (a p n : ℕ) (hn : 32 ≤ n) (hm : 3*p+1 < p+n) :
    IsZero (groupHomology (altColumn a (p+n) p) 1) := by
  have := alternatingStabilizer_perfect a p n hn
  exact (TrivialHomology.H1_isZero_of_perfect
    (G:=MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n))).of_iso
      (alternatingOrbitHomologyIso a p n hm 1)

lemma altBoundary_zero_H2_epi (a m : ℕ) (hm : 34 ≤ m) :
    Epi ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 2).map (altBoundary a m 0)) := by
  have := altBoundary_zero_epi a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 0 (altBoundary a m 2)) :=
    altBoundary_two_H0_isIso a m (by omega)
  have hz : IsZero (groupHomology (altColumn a m 2) 1) := by
    have he : m=2+(m-2) := by omega
    rw [he]
    exact altColumn_H1_isZero a 2 (m-2) (by omega) (by omega)
  exact BoundedHomologyEdge.chain_H2_epi (altBoundary a m 0) (altBoundary a m 1)
    (altBoundary a m 2) (altBoundary_square a m 0) (altBoundary_square a m 1)
    (altBoundary_exact a m 0 (by omega) (by omega))
    (altBoundary_exact a m 1 (by omega) (by omega)) hz

end PolygonPlacement.Configuration
end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonHomologyAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonHomologyAction

open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

theorem stabilize_fix_outside (g : polygonFullGroup a n) (x : TrackPoint a (k+n))
    (hx : x∉Set.range (rightIncl a k n)) : (stabilize a k n g).val x=x := by
  obtain ⟨y,rfl⟩ := (join a k n).surjective x
  cases y with
  | inl y => exact stabilize_left g y
  | inr y => exact False.elim (hx ⟨y,rfl⟩)

theorem conjugate_stabilize_eq (f c : polygonFullGroup a (k+n))
    (hc : ∀x : TrackPoint a n,c.val (rightIncl a k n x)=f.val (rightIncl a k n x))
    (g : polygonFullGroup a n) :
    f*stabilize a k n g*f⁻¹=c*stabilize a k n g*c⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := f.val.surjective y
  change f.val ((stabilize a k n g).val (f.val.symm (f.val x)))=
    c.val ((stabilize a k n g).val (c.val.symm (f.val x)))
  rw [f.val.symm_apply_apply]
  by_cases hx : x∈Set.range (rightIncl a k n)
  · obtain ⟨z,rfl⟩ := hx
    rw [←hc z,c.val.symm_apply_apply]
    change f.val ((stabilize a k n g).val (z.1.natAdd k,z.2))=
      c.val ((stabilize a k n g).val (z.1.natAdd k,z.2))
    rw [stabilize_right]
    exact (hc (g.val z)).symm
  · have hz : c.val.symm (f.val x)∉Set.range (rightIncl a k n) := by
      rintro ⟨z,hz⟩
      have hg : f.val (rightIncl a k n z)=f.val x := by
        rw [←hc z,hz,c.val.apply_symm_apply]
      exact hx ⟨z,f.val.injective hg⟩
    rw [stabilize_fix_outside g x hx,stabilize_fix_outside g _ hz,c.val.apply_symm_apply]

theorem conjugation_stabilize_inner (f : polygonFullGroup a (k+n)) (hm : 6*n+7<k+n) :
    ∃c : polygonAlternatingGroup a (k+n),
      (fullConjugation a (k+n) f).comp (stabilizeAlternating a k n)=
      (MulAut.conj c).toMonoidHom.comp (stabilizeAlternating a k n) := by
  obtain ⟨c,hc⟩ := exists_alternating_agrees_right f hm
  refine ⟨c,?_⟩
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  exact conjugate_stabilize_eq f c.val hc g.val

theorem mapH2_fullConjugation_comp_stabilize (f : polygonFullGroup a (k+n))
    (hm : 6*n+7<k+n) :
    (IntegralHomology.mapH2 (fullConjugation a (k+n) f)).comp
      (IntegralHomology.mapH2 (stabilizeAlternating a k n))=
      IntegralHomology.mapH2 (stabilizeAlternating a k n) := by
  obtain ⟨c,hc⟩ := conjugation_stabilize_inner f hm
  rw [←IntegralHomology.mapH2_comp,hc,IntegralHomology.mapH2_conjugate]

theorem mapH2_fullConjugation_eq_id_of_surjective
    (hm : 6*n+7<k+n)
    (hs : Function.Surjective (IntegralHomology.mapH2 (stabilizeAlternating a k n)))
    (f : polygonFullGroup a (k+n)) :
    IntegralHomology.mapH2 (fullConjugation a (k+n) f)=LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := hs z
  exact LinearMap.congr_fun (mapH2_fullConjugation_comp_stabilize f hm) w

end PolygonTracks
end PolygonHomologyAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AlternatingH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2
namespace PolygonPlacement.Configuration
variable {a m : ℕ}

lemma altAugmentation_pointMap (f : Configuration a m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) q).map (altBoundary a m 0) ≫
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) q).map (altEmptyIso a m).hom =
    TrivialHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso a m).hom.hom ((boundary a m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma alternatingStabilizer_H2_epi (a m : ℕ) (hm : 34 ≤ m) (f : Configuration a m 1) :
    Epi (TrivialHomology.map (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype 2) := by
  have := TransitiveInduction.isIso_map_pointMap f (fun g => alternating_transitive f g (by omega)) 2
  have first : Epi (groupHomology.map
      (MulAction.stabilizer (polygonAlternatingGroup a m) f).subtype
      (TransitiveInduction.pointMap f) 2) := inferInstance
  have second := altBoundary_zero_H2_epi a m hm
  have third : Epi ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 2).map
      (altEmptyIso a m).hom) := inferInstance
  rw [← altAugmentation_pointMap f 2]
  have composite := epi_comp' first (epi_comp' second third)
  exact composite

lemma stabilizeAlternating_H2_epi (a n : ℕ) (hn : 33 ≤ n) :
    Epi (TrivialHomology.map (PolygonTracks.stabilizeAlternating a 1 n) 2) := by
  rw [← alternatingStabilizerEquiv_subtype a 1 n (by omega), TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (alternatingStabilizerEquiv a 1 n (by omega)) 2
  have := alternatingStabilizer_H2_epi a (1+n) (by omega) (standard a 1 n)
  infer_instance
end PolygonPlacement.Configuration

namespace PolygonTracks

lemma stabilizeAlternating_add (a k l n : ℕ) : stabilizeAlternating a (k+l) n =
    (castAlternating a (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilizeAlternating a k (l+n)).comp (stabilizeAlternating a l n)) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  change stabilize a (k+l) n g.val=_
  rw [stabilize_add]
  simp only [MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom,
    castAlternating_val,stabilizeAlternating_val]

lemma stabilizeAlternating_zero_bijective (a n : ℕ) (hn : 32 ≤ n) :
    Function.Bijective (stabilizeAlternating a 0 n) := by
  refine ⟨stabilizeAlternating_injective,?_⟩
  intro g
  obtain ⟨f,hf⟩ := (stabilize_zero_bijective a n).surjective g.val
  have hg : f∈polygonAlternatingGroup a n := by
    rw [← stabilize_alternating_comap a 0 n hn]
    change stabilize a 0 n f∈polygonAlternatingGroup a (0+n)
    rw [hf]
    exact g.property
  exact ⟨⟨f,hg⟩,Subtype.ext hf⟩

lemma stabilizeAlternating_H2_epi (a k n : ℕ) (hn : 33 ≤ n) :
    Epi (TrivialHomology.map (stabilizeAlternating a k n) 2) := by
  induction k with
  | zero =>
      have : IsIso (TrivialHomology.map (stabilizeAlternating a 0 n) 2) :=
        TrivialHomology.isIso_equiv
        (MulEquiv.ofBijective (stabilizeAlternating a 0 n)
          (stabilizeAlternating_zero_bijective a n (by omega))) 2
      infer_instance
  | succ k ih =>
    have he : Epi (TrivialHomology.map (stabilizeAlternating a (1+k) n) 2) := by
      rw [stabilizeAlternating_add, TrivialHomology.map_comp, TrivialHomology.map_comp]
      have := TrivialHomology.isIso_equiv (castAlternating a (Nat.add_assoc 1 k n).symm) 2
      have := PolygonPlacement.Configuration.stabilizeAlternating_H2_epi a (k+n) (by omega)
      have := ih
      infer_instance
    rw [show k+1=1+k by omega]
    exact he

lemma stabilizeAlternating_mapH2_surjective (a k n : ℕ) (hn : 33 ≤ n) :
    Function.Surjective (IntegralHomology.mapH2 (stabilizeAlternating a k n)) := by
  have := stabilizeAlternating_H2_epi a k n hn
  exact (ModuleCat.epi_iff_surjective (TrivialHomology.map (stabilizeAlternating a k n) 2)).mp inferInstance

lemma fullAction_trivial (a m : ℕ) (hm : 205 < m) (f : polygonFullGroup a m) :
    IntegralHomology.mapH2 (fullConjugation a m f)=LinearMap.id := by
  obtain ⟨k,rfl⟩ : ∃k,m=k+33 := ⟨m-33,by omega⟩
  exact mapH2_fullConjugation_eq_id_of_surjective (by omega)
    (stabilizeAlternating_mapH2_surjective a k 33 (by omega)) f
end PolygonTracks
end SimpleAmenable

end

open _root_.CategoryTheory CategoryTheory.Limits

namespace FiniteHomologyReturn

section
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

lemma finite_of_exact {X : ShortComplex (ModuleCat.{u} R)} (hX : X.Exact)
    [Module.Finite R X.X₁] [Module.Finite R X.X₃] : Module.Finite R X.X₂ := by
  have : Module.Finite R (LinearMap.range X.g.hom) :=
    Module.Finite.of_injective (LinearMap.range X.g.hom).subtype Subtype.val_injective
  exact Module.Finite.of_exact (f:=X.f.hom) (g:=X.g.hom.rangeRestrict)
    (by
      rw [LinearMap.exact_iff]
      simpa using hX.moduleCat_range_eq_ker.symm)
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)

lemma finite_range_of_exact {A B C D : ModuleCat.{u} R}
    (p : A ⟶ B) (δ : B ⟶ C) (f : B ⟶ D) (w : p ≫ δ=0)
    (hex : (ShortComplex.mk p δ w).Exact) (hpf : p ≫ f=0)
    [Module.Finite R C] : Module.Finite R (LinearMap.range f.hom) := by
  have : Module.Finite R (LinearMap.range δ.hom) :=
    Module.Finite.of_injective (LinearMap.range δ.hom).subtype Subtype.val_injective
  have : Module.Finite R (B ⧸ LinearMap.ker δ.hom) :=
    Module.Finite.equiv δ.hom.quotKerEquivRange.symm
  have hk : LinearMap.ker δ.hom ≤ LinearMap.ker f.hom := by
    rw [← hex.moduleCat_range_eq_ker]
    exact LinearMap.range_le_ker_iff.mpr (ModuleCat.hom_ext_iff.mp hpf)
  let φ : (B ⧸ LinearMap.ker δ.hom) →ₗ[R] LinearMap.range f.hom :=
    (LinearMap.ker δ.hom).liftQ f.hom.rangeRestrict (by
      intro x hx
      exact Subtype.ext (hk hx))
  exact Module.Finite.of_surjective φ (by
    rintro ⟨y,x,rfl⟩
    exact ⟨(LinearMap.ker δ.hom).mkQ x,rfl⟩)

end

open BoundedHomologyEdge
variable {R G : Type} [CommRing R] [IsNoetherianRing R] [Group G]

variable {Z₁ Z₂ Z₃ C₀ C₁ C₂ C₃ C₄ : Rep R G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {i₃ : Z₃ ⟶ C₃} {p₃ : C₃ ⟶ Z₂}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0} {w₃ : i₃ ≫ p₃ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (h₃ : (ShortComplex.mk i₃ p₃ w₃).ShortExact)
  (e : C₄ ⟶ Z₃) [Epi e]

include h₁ h₂ h₃ e

lemma finite_H2 [Module.Finite R (groupHomology C₀ 2)]
    [Module.Finite R (groupHomology C₄ 0)]
    (hz₃ : IsZero (groupHomology C₃ 1))
    (hd : Hmap 2 (p₂ ≫ i₁)=0) : Module.Finite R (groupHomology C₁ 2) := by
  have : Module.Finite R ((groupHomology.functor R G 0).obj C₄) :=
    ‹Module.Finite R (groupHomology C₄ 0)›
  have : Module.Finite R ((groupHomology.functor R G 2).obj C₀) :=
    ‹Module.Finite R (groupHomology C₀ 2)›
  let : Epi (Hmap 0 e) := epi_Hmap_zero e
  have : Module.Finite R (groupHomology Z₃ 0) :=
    Module.Finite.of_surjective (Hmap 0 e).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  let : Mono (groupHomology.δ h₃ 1 0 rfl) :=
    (exact₃ h₃ 0).mono_g_iff.mpr (hz₃.eq_zero_of_src _)
  have : Module.Finite R (groupHomology Z₂ 1) :=
    Module.Finite.of_injective (groupHomology.δ h₃ 1 0 rfl).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite R (LinearMap.range (Hmap 2 i₁).hom) :=
    finite_range_of_exact (Hmap 2 p₂) (groupHomology.δ h₂ 2 1 rfl) (Hmap 2 i₁)
      (groupHomology.mapShortComplex₃ h₂ rfl).zero (exact₃ h₂ 1)
      (by rw [← Hmap_comp]; exact hd)
  exact finite_of_exact (X:=ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.range (Hmap 2 i₁).hom).subtype) (Hmap 2 p₁)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (Hmap 2 p₁).hom x.val=0
      exact (show LinearMap.range (Hmap 2 i₁).hom ≤ LinearMap.ker (Hmap 2 p₁).hom by
        rw [(exact₂ h₁ 2).moduleCat_range_eq_ker]) x.property))
    (by
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simpa using (exact₂ h₁ 2).moduleCat_range_eq_ker)

end FiniteHomologyReturn

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_QuotientRegular
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q)

lemma isIso_point (hf : Function.Surjective f) (n : ℕ) :
    IsIso (groupHomology.map f.ker.subtype (point f) n) := by
  let : MulAction G Q := MulAction.compHom Q f
  have ht : ∀q:Q,∃g:G,g • (1:Q)=q := by
    intro q
    obtain ⟨g,rfl⟩ := hf q
    exact ⟨g,mul_one _⟩
  have he : groupHomology.map f.ker.subtype (point f) n ≫
      groupHomology.map (MonoidHom.id G) (permutationIso f).hom n =
      TrivialHomology.map (kernelEquivStabilizer f).toMonoidHom n ≫
      groupHomology.map (MulAction.stabilizer G (1:Q)).subtype
        (TransitiveInduction.pointMap (1:Q)) n := by
    rw [← groupHomology.map_comp, ← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext g; rfl
    · apply LinearMap.ext; intro z; simp [point,permutationIso,TransitiveInduction.pointMap,TransitiveInduction.trivialMap]
  have := TrivialHomology.isIso_equiv (kernelEquivStabilizer f) n
  have := TransitiveInduction.isIso_map_pointMap (G:=G) (1:Q) ht n
  have : IsIso (groupHomology.map f.ker.subtype (point f) n ≫
      groupHomology.map (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
        (MonoidHom.id G) (permutationIso f).hom n) := by
    rw [he]
    infer_instance
  have : IsIso (groupHomology.map
      (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
      (MonoidHom.id G) (permutationIso f).hom n) :=
    inferInstanceAs (IsIso ((groupHomology.functor ℤ G n).mapIso (permutationIso f)).hom)
  exact IsIso.of_isIso_comp_right _
    (groupHomology.map (B:=Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)))
      (MonoidHom.id G) (permutationIso f).hom n)

lemma right_homology_identity (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _) (q : Q) :
    (groupHomology.functor ℤ G n).map (right f q)=𝟙 _ := by
  obtain ⟨g,rfl⟩ := hf q
  have := isIso_point f hf n
  apply (cancel_epi (groupHomology.map f.ker.subtype (point f) n)).mp
  change _ = groupHomology.map f.ker.subtype (point f) n ≫ 𝟙 (groupHomology (regular f) n)
  rw [Category.comp_id]
  have hc := HomologyConjugation.map_after_conjugation f.ker.subtype (point f) g n
  have he :
      groupHomology.map ((MulAut.conj g).toMonoidHom.comp f.ker.subtype)
        (point f ≫ (Rep.resFunctor f.ker.subtype).map
          (HomologyConjugation.conjugationCoeff g (regular f))) n =
      TrivialHomology.map (conjugate f g).toMonoidHom n ≫
        groupHomology.map f.ker.subtype (point f) n ≫
        (groupHomology.functor ℤ G n).map (right f (f g)) := by
    dsimp only [groupHomology.functor]
    rw [← groupHomology.map_comp, ← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext h; rfl
    · apply LinearMap.ext
      intro z
      simp [point,right,TransitiveInduction.trivialMap,
        HomologyConjugation.conjugationCoeff,regular,Representation.ofMulAction_def]
  rw [he,hact,Category.id_comp] at hc
  exact hc

lemma H1_isZero (hf : Function.Surjective f)
    (hz : IsZero (groupHomology (Rep.trivial ℤ f.ker ℤ) 1)) :
    IsZero (groupHomology (regular f) 1) := by
  have := isIso_point f hf 1
  exact hz.of_iso (asIso (groupHomology.map f.ker.subtype (point f) 1)).symm

lemma H2_finite_of_regular (hf : Function.Surjective f)
    [Module.Finite ℤ (groupHomology (regular f) 2)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) := by
  have := isIso_point f hf 2
  exact Module.Finite.of_injective (groupHomology.map f.ker.subtype (point f) 2).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

end QuotientRegular

end

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Finsupp
namespace FiniteFreeRep

attribute [local instance 1200] Rep.hV2
variable {k Q : Type} [CommRing k] [Group Q]

lemma sum_proj_incl (A : Rep.{0} k Q) (n : ℕ) :
    ∑ i:Fin n,proj A i ≫ incl A i=𝟙 (Rep.finsupp (Fin n) A) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro i x
  simp [Rep.sum_hom, incl,proj,Representation.IntertwiningMap.sum_apply]

lemma functor_isZero (F : Rep.{0} k Q ⥤ ModuleCat k) [F.Additive]
    (A : Rep.{0} k Q) (h : IsZero (F.obj A)) (n : ℕ) : IsZero (F.obj (Rep.finsupp (Fin n) A)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← F.map_id, ← sum_proj_incl,F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [F.map_comp,h.eq_zero_of_tgt (F.map (proj A i)),zero_comp]

lemma functor_finite [IsNoetherianRing k] (F : Rep.{0} k Q ⥤ ModuleCat k) [F.Additive]
    (A : Rep.{0} k Q) [Module.Finite k (F.obj A)] (n : ℕ) :
    Module.Finite k (F.obj (Rep.finsupp (Fin n) A)) := by
  let φ : F.obj (Rep.finsupp (Fin n) A) →ₗ[k] (Fin n → F.obj A) :=
    LinearMap.pi (fun i => (F.map (proj A i)).hom)
  apply Module.Finite.of_injective φ
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hp : ∀i:Fin n,(F.map (proj A i)).hom x=0 := fun i => congrFun hx i
  have he : ∑ i:Fin n,(F.map (proj A i) ≫ F.map (incl A i))=𝟙 _ := by
    simp only [← F.map_comp, ← F.map_sum,sum_proj_incl,F.map_id]
  have ht := congrArg (fun t => t.hom x) he
  simpa [hp] using ht.symm

lemma exists_cover (A : Rep.{0} k Q)
    [Module.Finite (MonoidAlgebra k Q) A.ρ.asModule] :
    ∃n:ℕ,∃e:Rep.free k Q (Fin n) ⟶ A,Epi e := by
  obtain ⟨n,φ,hφ⟩ := Module.Finite.exists_fin' (MonoidAlgebra k Q) A.ρ.asModule
  let ψ : (Rep.free k Q (Fin n)).ρ.asModule →ₗ[MonoidAlgebra k Q] A.ρ.asModule :=
    φ.comp ((Finsupp.linearEquivFunOnFinite (MonoidAlgebra k Q) (MonoidAlgebra k Q) (Fin n)).toLinearMap.comp
      (Representation.finsuppLEquivFreeAsModule k Q (Fin n)).symm.toLinearMap)
  have hψ : Function.Surjective ψ := hφ.comp
    ((Finsupp.linearEquivFunOnFinite (MonoidAlgebra k Q) (MonoidAlgebra k Q) (Fin n)).surjective.comp
      (Representation.finsuppLEquivFreeAsModule k Q (Fin n)).symm.surjective)
  let p : Rep.toModuleMonoidAlgebra.obj (Rep.free k Q (Fin n)) ⟶ Rep.toModuleMonoidAlgebra.obj A :=
    ModuleCat.ofHom ψ
  have : Epi p := (ModuleCat.epi_iff_surjective _).mpr hψ
  let e : Rep.free k Q (Fin n) ⟶ A :=
    (Rep.unitIso _).hom ≫ Rep.ofModuleMonoidAlgebra.map p ≫ (Rep.unitIso _).inv
  exact ⟨n,e,by dsimp only [e]; infer_instance⟩

lemma finite_kernel {A B : Rep.{0} k Q} (d : A ⟶ B)
    [IsNoetherianRing (MonoidAlgebra k Q)]
    [Module.Finite (MonoidAlgebra k Q) A.ρ.asModule] :
    Module.Finite (MonoidAlgebra k Q) (kernel d).ρ.asModule := by
  have : Module.Finite (MonoidAlgebra k Q) (Rep.toModuleMonoidAlgebra.obj A) :=
    ‹Module.Finite (MonoidAlgebra k Q) A.ρ.asModule›
  let p := Rep.toModuleMonoidAlgebra.map (kernel.ι d)
  have : Mono p := inferInstanceAs (Mono (Rep.toModuleMonoidAlgebra.map (kernel.ι d)))
  exact Module.Finite.of_injective p.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)

end FiniteFreeRep

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

lemma regular_ext {A : Rep ℤ Q} (t u : Rep.leftRegular ℤ Q ⟶ A)
    (h : t.hom (MonoidAlgebra.single 1 1)=u.hom (MonoidAlgebra.single 1 1)) : t=u := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext
  intro z
  have ht := congrArg (fun T => T (MonoidAlgebra.single 1 1)) (t.hom.isIntertwining' q)
  have hu := congrArg (fun T => T (MonoidAlgebra.single 1 1)) (u.hom.isIntertwining' q)
  have hv : t.hom (MonoidAlgebra.single q 1)=u.hom (MonoidAlgebra.single q 1) := by
    change t.hom ((Rep.leftRegular ℤ Q).ρ q (MonoidAlgebra.single 1 1)) = A.ρ q (t.hom (MonoidAlgebra.single 1 1)) at ht
    change u.hom ((Rep.leftRegular ℤ Q).ρ q (MonoidAlgebra.single 1 1)) = A.ρ q (u.hom (MonoidAlgebra.single 1 1)) at hu
    rw [h] at ht
    simpa using ht.trans hu.symm
  change t.hom (MonoidAlgebra.single q z)=u.hom (MonoidAlgebra.single q z)
  have he : MonoidAlgebra.single q z = z • (MonoidAlgebra.single q 1 : MonoidAlgebra ℤ Q) := by simp
  rw [he]
  change t.hom.toLinearMap _ = u.hom.toLinearMap _
  rw [LinearMap.map_smul,LinearMap.map_smul]
  exact congrArg _ hv

lemma regular_sum_right (t : Rep.leftRegular ℤ Q ⟶ Rep.leftRegular ℤ Q) :
    t = ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
      (t.hom (MonoidAlgebra.single 1 1)).coeff q • right (MonoidHom.id Q) q := by
  apply regular_ext
  simp only [Rep.sum_hom,Rep.zsmul_hom,Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply]
  change _ = ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
    (t.hom (MonoidAlgebra.single 1 1)).coeff q •
      (right (MonoidHom.id Q) q).hom (MonoidAlgebra.single 1 1)
  have hr (q:Q) : (right (MonoidHom.id Q) q).hom (MonoidAlgebra.single 1 1)=
      MonoidAlgebra.single q 1 := by simpa using right_single (MonoidHom.id Q) q 1 1
  simp only [hr,MonoidAlgebra.smul_single,smul_eq_mul,mul_one]
  simpa only [Finsupp.sum] using
    (MonoidAlgebra.sum_coeff_single (t.hom (MonoidAlgebra.single 1 1))).symm

lemma map_regular_zero (f : G →* Q) (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _)
    (t : Rep.leftRegular ℤ Q ⟶ Rep.leftRegular ℤ Q) (ht : t ≫ augment=0) :
    (groupHomology.functor ℤ G n).map ((Rep.resFunctor f).map t)=0 := by
  let F := Rep.resFunctor f ⋙ groupHomology.functor ℤ G n
  have ha : ∑q∈(t.hom (MonoidAlgebra.single 1 1)).coeff.support,
      (t.hom (MonoidAlgebra.single 1 1)).coeff q=0 := by
    have hh := congrArg (fun s => s.hom (MonoidAlgebra.single 1 1)) ht
    simpa [augment,MonoidAlgebra.lift_apply,Finsupp.sum] using hh
  change F.map t=0
  rw [regular_sum_right t,F.map_sum]
  simp_rw [F.map_zsmul]
  have hr : ∀q:Q,F.map (right (MonoidHom.id Q) q)=𝟙 _ := fun q =>
    right_homology_identity f hf n hact q
  simp_rw [hr]
  rw [← Finset.sum_smul,ha,zero_smul]

lemma map_free_zero (f : G →* Q) (hf : Function.Surjective f) (n : ℕ)
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom n=𝟙 _)
    (k : ℕ) (t : Rep.free ℤ Q (Fin k) ⟶ Rep.leftRegular ℤ Q) (ht : t ≫ augment=0) :
    (groupHomology.functor ℤ G n).map ((Rep.resFunctor f).map t)=0 := by
  let F := Rep.resFunctor f ⋙ groupHomology.functor ℤ G n
  have hi : ∀i:Fin k,F.map (FiniteFreeRep.incl (Rep.leftRegular ℤ Q) i ≫ t)=0 := by
    intro i
    exact map_regular_zero f hf n hact _ (by rw [Category.assoc,ht,comp_zero])
  change F.map t=0
  rw [← Category.id_comp t,← FiniteFreeRep.sum_proj_incl (Rep.leftRegular ℤ Q) k,
    Preadditive.sum_comp,F.map_sum]
  apply Finset.sum_eq_zero
  intro i hi'
  rw [Category.assoc,F.map_comp,hi,comp_zero]

end QuotientRegular

end

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

lemma H0_finite (f : G →* Q) (hf : Function.Surjective f) :
    Module.Finite ℤ (groupHomology (regular f) 0) := by
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 0) :=
    Module.Finite.of_surjective
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ f.ker ℤ)).inv.hom
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ f.ker ℤ)).toLinearEquiv.symm.surjective
  have := isIso_point f hf 0
  exact Module.Finite.of_surjective (groupHomology.map f.ker.subtype (point f) 0).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma finite_kernel_H2 (f : G →* Q) (hf : Function.Surjective f)
    [IsNoetherianRing (MonoidAlgebra ℤ Q)]
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 2)]
    (hz : IsZero (groupHomology (Rep.trivial ℤ f.ker ℤ) 1))
    (hact : ∀g:G,TrivialHomology.map (conjugate f g).toMonoidHom 2=𝟙 _) :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) := by
  let ε := augment (Q:=Q)
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel ε).ρ.asModule :=
    FiniteFreeRep.finite_kernel ε
  obtain ⟨n₂,e₂,he₂⟩ := FiniteFreeRep.exists_cover (kernel ε)
  let := he₂
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel e₂).ρ.asModule :=
    FiniteFreeRep.finite_kernel e₂
  obtain ⟨n₃,e₃,he₃⟩ := FiniteFreeRep.exists_cover (kernel e₂)
  let := he₃
  have : Module.Finite (MonoidAlgebra ℤ Q) (kernel e₃).ρ.asModule :=
    FiniteFreeRep.finite_kernel e₃
  obtain ⟨n₄,e₄,he₄⟩ := FiniteFreeRep.exists_cover (kernel e₃)
  let := he₄
  let T : Rep.{0} ℤ Q ⥤ Rep.{0} ℤ G := Rep.resFunctor f
  let F₀ := T ⋙ groupHomology.functor ℤ G 0
  let F₁ := T ⋙ groupHomology.functor ℤ G 1
  have : Module.Finite ℤ (F₀.obj (Rep.leftRegular ℤ Q)) := H0_finite f hf
  have : Module.Finite ℤ (groupHomology (T.obj (Rep.free ℤ Q (Fin n₄))) 0) :=
    FiniteFreeRep.functor_finite F₀ (Rep.leftRegular ℤ Q) n₄
  have hz₃ : IsZero (groupHomology (T.obj (Rep.free ℤ Q (Fin n₃))) 1) :=
    FiniteFreeRep.functor_isZero F₁ (Rep.leftRegular ℤ Q) (H1_isZero f hf hz) n₃
  have hd : BoundedHomologyEdge.Hmap 2 (T.map e₂ ≫ T.map (kernel.ι ε))=0 := by
    rw [← T.map_comp]
    exact map_free_zero f hf 2 hact n₂ (e₂ ≫ kernel.ι ε)
      (by rw [Category.assoc,kernel.condition,comp_zero])
  let e₀ : Rep.trivial ℤ G ℤ ≅ T.obj (Rep.trivial ℤ Q ℤ) :=
    Rep.mkIso (.mk (LinearEquiv.refl ℤ ℤ) (by intro g; rfl))
  let eH := (groupHomology.functor ℤ G 2).mapIso e₀
  have : Module.Finite ℤ ((groupHomology.functor ℤ G 2).obj (Rep.trivial ℤ G ℤ)) :=
    inferInstanceAs (Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 2))
  have : Module.Finite ℤ (groupHomology (T.obj (Rep.trivial ℤ Q ℤ)) 2) :=
    Module.Finite.of_surjective eH.hom.hom eH.toLinearEquiv.surjective
  have : Epi (T.map e₄) := (Rep.epi_iff_surjective _).mpr
    ((Rep.epi_iff_surjective e₄).mp he₄)
  have : Module.Finite ℤ (groupHomology (regular f) 2) :=
    FiniteHomologyReturn.finite_H2
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact ε))
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact e₂))
      ((Rep.shortExact_res f).mpr (BoundedHomologyEdge.kernel_shortExact e₃))
      (T.map e₄) hz₃ hd
  exact H2_finite_of_regular f hf

end QuotientRegular

end

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

lemma abelianization_ring_noetherian
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] :
    IsNoetherianRing (MonoidAlgebra ℤ (Abelianization G)) := by
  have := abelianization_fg G
  have : Algebra.FiniteType ℤ (MonoidAlgebra ℤ (Abelianization G)) :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ _
end TrivialHomology

namespace PolygonTracks

lemma finite_alternating_H2_of_full_oai (a m : ℕ) (hm : 205 < m)
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1)]
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2)] :
    Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m))) := by
  let f : polygonFullGroup a m →* Abelianization (polygonFullGroup a m) := Abelianization.of
  let e := abelianKernelEquiv a m (by omega)
  have : IsNoetherianRing (MonoidAlgebra ℤ (Abelianization (polygonFullGroup a m))) :=
    TrivialHomology.abelianization_ring_noetherian _
  have : Group.IsPerfect (polygonAlternatingGroup a m) := polygonAlternatingGroup_perfect a m (by omega)
  have : Group.IsPerfect f.ker := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  have ha : ∀g : polygonFullGroup a m,
      TrivialHomology.map (QuotientRegular.conjugate f g).toMonoidHom 2 = 𝟙 _ := by
    intro g
    have := TrivialHomology.isIso_equiv e 2
    apply (cancel_mono (TrivialHomology.map e.toMonoidHom 2)).mp
    rw [Category.id_comp, ← TrivialHomology.map_comp]
    have he : e.toMonoidHom.comp (QuotientRegular.conjugate f g).toMonoidHom =
        (fullConjugation a m g).comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      rfl
    rw [he,TrivialHomology.map_comp]
    have hg : TrivialHomology.map (fullConjugation a m g) 2=𝟙 _ := by
      apply ModuleCat.hom_ext
      exact fullAction_trivial a m hm g
    rw [hg,Category.comp_id]
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) :=
    QuotientRegular.finite_kernel_H2 f (QuotientGroup.mk'_surjective _)
      (TrivialHomology.H1_isZero_of_perfect) ha
  have := TrivialHomology.isIso_equiv e 2
  exact Module.Finite.of_surjective (TrivialHomology.map e.toMonoidHom 2).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end PolygonTracks
end SimpleAmenable

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full_oai := @OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full_oai
