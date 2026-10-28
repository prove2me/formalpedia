-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.chart_action_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:59:16.04098+00:00
-- url     : https://prove2.me/submissions/04a07511-3096-4a25-bcd0-ccfeee3f7d1c

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

theorem conj_mul_of_commute (a b k : H) (h : Commute b k) :
    (a*b)*k*(a*b)⁻¹ = a*k*a⁻¹ := by
  calc
    _ = a*(b*k*b⁻¹)*a⁻¹ := by group
    _ = a*k*a⁻¹ := by rw [h.eq]; group

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

end SmallControlTransfer

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntersectionControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section IntersectionControl
namespace ActualLawfulTable
variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_split (U V : Set Ω) (s : UniversalExtension E) :
    T.sector U s = T.sector (U ∩ V) s*T.sector (U \ V) s := by
  have hd : Disjoint (U ∩ V) (U \ V) := Set.disjoint_left.mpr (by aesop)
  have he : (U ∩ V) ∪ (U \ V) = U := by ext x; simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]; tauto
  have hh := DFunLike.congr_fun (T.sector_union hd) s
  simpa only [he,commutingProduct_apply] using hh

end ActualLawfulTable

variable {α H Q Ω : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]
    {q : H →* Q} {v : (Ω → alternatingGroup α) →* Q}
    (T : ActualLawfulTable q v) (c : alternatingGroup α →* H)

variable {a : ℕ} {ι : Type*}

theorem resolvedPolygonMask_inter (U : ι → polygonAlgebra a) (V W : Set (GenericSquare a))
    (hV : ResolvedBy (fun i => (U i).val) V) (hW : ResolvedBy (fun i => (U i).val) W) :
    resolvedPolygonMask U (V ∩ W) = resolvedPolygonMask U V ∩ resolvedPolygonMask U W := by
  ext ω
  obtain ⟨x,hx⟩ := ω.property
  obtain rfl : ω = ⟨polygonAssignment U x,⟨x,rfl⟩⟩ := Subtype.ext hx.symm
  have hVW : ResolvedBy (fun i => (U i).val) (V ∩ W) := by
    intro x y he
    exact and_congr (hV x y he) (hW x y he)
  simp only [Set.mem_inter_iff,resolvedPolygonMask_mem U _ hVW x,
    resolvedPolygonMask_mem U _ hV x,resolvedPolygonMask_mem U _ hW x]

end IntersectionControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ChartQuadrants
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

section ChartAction
namespace ActualLawfulTable
variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_same_action (U V W : Set Ω) (he : U ∩ W = V ∩ W) :
    SameActionOn (T.sector U) (T.sector V) (T.sector W).range := by
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  rw [T.sector_split U W s,T.sector_split V W s]
  rw [conj_mul_of_commute _ _ _
    (T.sector_commute (Set.disjoint_left.mpr (by aesop)) s t)]
  rw [conj_mul_of_commute _ _ _
    (T.sector_commute (Set.disjoint_left.mpr (by aesop)) s t)]
  rw [he]
end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_same_action (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U V W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (he : U ⊓ W = V ⊓ W) :
    SameActionOn (B.fullGeometricSector hlarge P h U)
      (B.fullGeometricSector hlarge P h V) (B.fullGeometricSector hlarge P h W).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_same_action
  rw [← resolvedPolygonMask_inter _ U.val W.val hU hW,
    ← resolvedPolygonMask_inter _ V.val W.val hV hW]
  exact congrArg (resolvedPolygonMask (primitiveTests (a := a) (r := r) P))
    (congrArg Subtype.val he)

theorem chart_action_transfer_oai (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U V W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (he : U ⊓ W = V ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hcontrol : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h V (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  apply small_control_comparison _ B.c B.constant_aligned B.disjoint_aligned f _ hf hcontrol I.val _ _
    (B.fullGeometricSector_supported (by omega) P h U hU I ⟨s,rfl⟩)
    (B.fullGeometricSector_supported (by omega) P h V hV I ⟨s,rfl⟩)
    (by have hh := I.property.2; simp only [Fintype.card_fin]; omega)
  intro J t
  exact B.fullGeometricSector_same_action (by omega) P h U V W hU hV hW he _ _ ⟨_,rfl⟩

end InitialCoverSystem
end ChartAction

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.chart_action_transfer_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.chart_action_transfer_oai.{u_1}
