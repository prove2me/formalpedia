-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.control_trans
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:59:39.200415+00:00
-- url     : https://prove2.me/submissions/00f16f01-be82-48c6-aa5e-b72b9f4ca2e9

import Mathlib
import Definitions.Def_OAIQ65Sa011

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_NestedCutCalculus
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
section ConditionalControl
variable {E H : Type*} [Group E] [Group H]

theorem same_conj_iff (u v k : H) :
    u*k*u⁻¹ = v*k*v⁻¹ ↔ Commute (u⁻¹*v) k := by
  constructor
  · intro h
    apply commutatorElement_eq_one_iff_commute.mp
    rw [commutatorElement_def]
    calc
      _ = u⁻¹*(v*k*v⁻¹)*u*k⁻¹ := by group
      _ = u⁻¹*(u*k*u⁻¹)*u*k⁻¹ := by rw [← h]
      _ = 1 := by group
  · intro h
    have hc := h.eq
    calc
      u*k*u⁻¹ = u*(k*(u⁻¹*v))*v⁻¹ := by group
      _ = u*((u⁻¹*v)*k)*v⁻¹ := by rw [hc]
      _ = v*k*v⁻¹ := by group

theorem commute_of_conditional_move (u v k : H) (hv : Commute u v)
    (hk : Commute u (v*k*v⁻¹)) : Commute u k := by
  have h := (hv.inv_right.mul_right hk).mul_right hv
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h

end ConditionalControl

end SimpleAmenable
end
end

end OAI
end

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

theorem fresh_five_bank {α : Type*} [Fintype α] [DecidableEq α] (J : Finset α)
    (hJ : J.card + 5 ≤ Fintype.card α) :
    ∃ t : Fin 5 ↪ α, Disjoint (Finset.univ.map t) J := by
  classical
  have hc : 5 ≤ Jᶜ.card := by rw [Finset.card_compl]; omega
  have he : Nonempty (Fin 5 ↪ {x : α // x ∈ Jᶜ}) := by
    rw [Function.Embedding.nonempty_iff_card_le,Fintype.card_fin,Fintype.card_coe]
    exact hc
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Function.Embedding.subtype _),?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
  exact Finset.mem_compl.mp (e i).property hj

theorem even_move_disjoint_banks {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Fin 5 ↪ α) (hd : Disjoint (Finset.univ.map s) (Finset.univ.map t)) :
    ∃ σ : alternatingGroup α,
      (∀ i, σ.val (s i) = t i) ∧
      σ.val.support ⊆ (Finset.univ.map s) ∪ (Finset.univ.map t) := by
  classical
  let S := (Finset.univ.map s) ∪ (Finset.univ.map t)
  let T := {x : α // x ∈ S}
  let s' : Fin 5 ↪ T := ⟨fun i => ⟨s i,Finset.mem_union_left _ (Finset.mem_map.mpr
    ⟨i,Finset.mem_univ _,rfl⟩)⟩,fun _ _ h => s.injective (congrArg Subtype.val h)⟩
  let t' : Fin 5 ↪ T := ⟨fun i => ⟨t i,Finset.mem_union_right _ (Finset.mem_map.mpr
    ⟨i,Finset.mem_univ _,rfl⟩)⟩,fun _ _ h => t.injective (congrArg Subtype.val h)⟩
  have hT : Nat.card T = 10 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    dsimp only [S]
    rw [Finset.card_union_of_disjoint hd,Finset.card_map,Finset.card_map]
    simp
  obtain ⟨ρ,hρ⟩ := even_move_embedding (by omega : 5+2 ≤ Nat.card T) s' t'
  let e : T ↪ α := Function.Embedding.subtype _
  let σ := ρ.val.viaEmbedding e
  have hσ : σ ∈ alternatingGroup α := by
    change Equiv.Perm.sign (ρ.val.viaEmbedding e) = 1
    rw [Equiv.Perm.viaEmbedding,Equiv.Perm.sign_extendDomain]
    exact ρ.property
  refine ⟨⟨σ,hσ⟩,?_,?_⟩
  · intro i
    change ρ.val.viaEmbedding e (e (s' i)) = t i
    rw [Equiv.Perm.viaEmbedding_apply,hρ]
    rfl
  · intro x hx
    by_contra hn
    have he : x ∉ Set.range e := by
      rintro ⟨y,rfl⟩
      exact hn y.property
    exact Equiv.Perm.mem_support.mp hx (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he)

end FreshEvenBank

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OperationalControl
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
section OperationalControl

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem fresh_bank_conditional_control (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (s : Fin 5 ↪ α) (J : Finset α) (u x : H) (hu : u ∈ L J)
    (hx : x ∈ L (Finset.univ.map s))
    (hreserve : (J ∪ Finset.univ.map s).card + 5 ≤ Fintype.card α)
    (hv : ∀ (σ : alternatingGroup α), σ.val.support.card ≤ 10 →
      ∃ v : H, Commute u v ∧ v*x*v⁻¹ = c σ*x*(c σ)⁻¹) : Commute u x := by
  obtain ⟨t,ht⟩ := fresh_five_bank (J ∪ Finset.univ.map s) hreserve
  have hst : Disjoint (Finset.univ.map s) (Finset.univ.map t) :=
    (ht.mono_right Finset.subset_union_right).symm
  obtain ⟨σ,hσ,hsupp⟩ := even_move_disjoint_banks s t hst
  have hcard : σ.val.support.card ≤ 10 := by
    apply (Finset.card_le_card hsupp).trans
    rw [Finset.card_union_of_disjoint hst,Finset.card_map,Finset.card_map]
    simp
  obtain ⟨v,huv,hv⟩ := hv σ hcard
  apply commute_of_conditional_move u v x huv
  rw [hv]
  have hem : (Finset.univ.map s).map σ.val.toEmbedding = Finset.univ.map t := by
    rw [Finset.map_map]
    congr 1
    exact Function.Embedding.ext hσ
  have hm := hc σ (Finset.univ.map s) x hx
  rw [hem] at hm
  exact hd J (Finset.univ.map t) (ht.mono_right Finset.subset_union_left).symm u hu _ hm

end OperationalControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlCalculus
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
section SmallControlCalculus
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

omit [Fintype α] [DecidableEq α] [Group.IsPerfect (alternatingGroup α)] in
theorem five_bank_of_card (I : Finset α) (hI : I.card = 5) :
    ∃ s : Fin 5 ↪ α, Finset.univ.map s = I := by
  classical
  let e : Fin 5 ≃ I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let s := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ I))
  refine ⟨s,?_⟩
  ext x
  constructor
  · rintro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact (e i).property
  · intro hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩

omit [Group.IsPerfect (alternatingGroup α)] in

theorem small_star_representative (hα : 10 ≤ Fintype.card α)
    (σ : alternatingGroup α) (hσ : σ.val.support.card ≤ 10) :
    ∃ (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)),
      subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) t) = σ := by
  obtain ⟨I,hSI,_,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ σ.val.support) hσ (by simpa using hα)
  let J : ControlAlphabet α := ⟨I,by omega,by omega⟩
  obtain ⟨s,hs⟩ := (subtypeAlternatingHom_mem_range I σ).mpr hSI
  let := alphabetPerfect I (by omega)
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup J.val) s
  exact ⟨J,t,by simpa only [ht] using hs⟩

theorem small_control_transfer (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (f g : TrackStar α →* H) (hf : SmallSupported L f) (hfg : SmallControlled c f g)
    (J : Finset α) (u : H) (hu : u ∈ L J) (hreserve : J.card+10 ≤ Fintype.card α)
    (hug : ∀ (I : ControlAlphabet α) t, Commute u (g (universalMap (subtypeAlternatingHom I.val) t))) :
    ∀ x ∈ f.range, Commute u x := by
  classical
  let C := Subgroup.centralizer ({u} : Set H)
  have hC : f.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩
    let A : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,by have hh := I.property.2; omega⟩
    have hx : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L I.val :=
      hf A ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := five_bank_of_card I.val I.property.2
    have hx' : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L (Finset.univ.map s) := by
      rwa [hs]
    have hres : (J ∪ Finset.univ.map s).card + 5 ≤ Fintype.card α := by
      rw [hs]
      have hh := Finset.card_union_le J I.val
      rw [I.property.2] at hh
      omega
    have hh := fresh_bank_conditional_control L c hc hd s J u
      (f (universalMap (subtypeAlternatingHom I.val) t)) hu hx' hres ?_
    · intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hh.eq
    · intro σ hσ
      obtain ⟨K,v,hv⟩ := small_star_representative (by omega : 10 ≤ Fintype.card α) σ hσ
      refine ⟨g (universalMap (subtypeAlternatingHom K.val) v),hug K v,?_⟩
      have hh := hfg K v _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩
      have he := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom K.val)) v
      change universalProjection (alternatingGroup α) (universalMap (subtypeAlternatingHom K.val) v) = _ at he
      simpa only [MonoidHom.comp_apply,he,hv] using hh
  intro x hx
  exact hC hx u (Set.mem_singleton u)

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
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
section FullSectorSupport
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem constant_small_supported :
    SmallSupported (sourceAlignedGroup a r m hm M B.t)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))) := by
  intro I
  rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,← B.initialAlphabet_zero]
  rintro x ⟨t,rfl⟩
  exact B.initialAlphabet_aligned I.val 0 _

end InitialCoverSystem
end FullSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlTransfer
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
section SmallControlTransfer
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)

include hc hd in

theorem small_control_comparison (f g : TrackStar α →* H)
    (hf : SmallSupported L f) (hfg : SmallControlled c f g)
    (J : Finset α) (u v : H) (hu : u ∈ L J) (hv : v ∈ L J)
    (hreserve : J.card+10 ≤ Fintype.card α)
    (hact : ∀ (I : ControlAlphabet α) t,
      u*g (universalMap (subtypeAlternatingHom I.val) t)*u⁻¹ =
        v*g (universalMap (subtypeAlternatingHom I.val) t)*v⁻¹) :
    ∀ x ∈ f.range, u*x*u⁻¹ = v*x*v⁻¹ := by
  have hh := small_control_transfer L c hc hd f g hf hfg J (u⁻¹*v)
    ((L J).mul_mem ((L J).inv_mem hu) hv) hreserve
    (fun I t => (same_conj_iff _ _ _).mp (hact I t))
  intro x hx
  exact (same_conj_iff _ _ _).mpr (hh x hx)

include hc hd in

theorem small_control_trans (hα : 20 ≤ Fintype.card α)
    (hconst : SmallSupported L (c.comp (universalProjection (alternatingGroup α))))
    (f g k : TrackStar α →* H) (hf : SmallSupported L f) (hk : SmallSupported L k)
    (hfg : SmallControlled c f g) (hgk : SmallControlled c g k) :
    SmallControlled c f k := by
  intro I t x hx
  apply small_control_comparison L c hc hd f g hf hfg I.val
    (k (universalMap (subtypeAlternatingHom I.val) t))
    (c (universalProjection (alternatingGroup α) (universalMap (subtypeAlternatingHom I.val) t)))
    (hk I ⟨t,rfl⟩) (hconst I ⟨t,rfl⟩) (by have hh := I.property.2; omega) ?_ x hx
  intro J s
  exact hgk I t _ ⟨universalMap (subtypeAlternatingHom J.val) s,rfl⟩

end SmallControlTransfer

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ControlCalculus
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
section SourceControlCalculus
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem control_trans_oai (hlarge : 20 ≤ m+1)
    (f g k : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f) (hk : B.AlignedSmallSupported k)
    (hfg : SmallControlled B.c f g) (hgk : SmallControlled B.c g k) :
    SmallControlled B.c f k :=
  small_control_trans _ B.c B.constant_aligned B.disjoint_aligned (by simpa using hlarge)
    B.constant_small_supported f g k hf hk hfg hgk

end InitialCoverSystem
end SourceControlCalculus

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.control_trans_oai := @OAI.SimpleAmenable.InitialCoverSystem.control_trans_oai
