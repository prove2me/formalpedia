-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.gridInputs_normalize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:54:06.350734+00:00
-- url     : https://prove2.me/submissions/f86fd869-e5f1-4da4-b428-23e8f3f4b8ad

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ResolvedBoolean
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
section ResolvedBoolean

variable {X ι : Type*}

variable {a : ℕ}

theorem resolvedPolygonMask_mono (U : ι → polygonAlgebra a)
    {V W : Set (GenericSquare a)} (h : V ⊆ W) :
    resolvedPolygonMask U V ⊆ resolvedPolygonMask U W := by
  rintro ω ⟨x,he,hx⟩
  exact ⟨x,he,h hx⟩

end ResolvedBoolean

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
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
section ActualSectorControl

variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]

namespace ActualLawfulTable
variable {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_control {U V : Set Ω} (hUV : U ⊆ V) :
    SameActionOn (T.sector V) (T.sector Set.univ) (T.sector U).range := by
  classical
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  have hd : Disjoint V Vᶜ := disjoint_compl_right_iff.mpr le_rfl
  have he := DFunLike.congr_fun (T.sector_union hd) s
  rw [Set.union_compl_self] at he
  rw [he]
  change _ = (T.sector V s*T.sector Vᶜ s) * _ * (T.sector V s*T.sector Vᶜ s)⁻¹
  exact (conj_mul_of_commute _ _ _
    (T.sector_commute (disjoint_compl_left_iff.mpr hUV) s t)).symm

end ActualLawfulTable

variable {a : ℕ} {ι : Type*}

theorem resolvedPolygonMask_univ (U : ι → polygonAlgebra a) :
    resolvedPolygonMask U Set.univ = Set.univ := by
  ext ω
  simp only [resolvedPolygonMask,Set.mem_ofPred_eq,Set.mem_univ,iff_true,and_true]
  exact ω.property

end ActualSectorControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSectorCompatibility
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
section FullSectorCompatibility
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SameActionOn (B.fullGeometricSector hlarge P h W)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
      (B.fullGeometricSector hlarge P h V).range := by
  rw [← B.fullGeometricSector_whole hlarge P h]
  unfold fullGeometricSector
  change SameActionOn _ ((B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) Set.univ)) _
  rw [resolvedPolygonMask_univ]
  exact (B.fullPrimitiveTable hlarge P h).sector_control (resolvedPolygonMask_mono _ hVW)

end InitialCoverSystem
end FullSectorCompatibility

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

theorem fullGeometricSector_small_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SmallControlled B.c (B.fullGeometricSector hlarge P h V) (B.fullGeometricSector hlarge P h W) := by
  intro I t x hx
  exact B.fullGeometricSector_control hlarge P h V W hVW _ x hx

theorem fullGeometricSector_commute (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hVW : Disjoint V.val W.val)
    (s t : UniversalExtension (alternatingGroup (Fin (m+1)))) :
    Commute (B.fullGeometricSector hlarge P h V s) (B.fullGeometricSector hlarge P h W t) :=
  (B.fullPrimitiveTable hlarge P h).sector_commute (resolvedPolygonMask_disjoint _ hV hVW) s t

end InitialCoverSystem
end FullSectorSupport

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

theorem normalizes_of_cell_split (P : Subgroup G) (x y z : G)
    (hx : x=y*z) (hy : y ∈ P) (hz : z ∈ Subgroup.centralizer (P : Set G)) :
    x ∈ (Subgroup.normalizer (P : Set G)) := by
  rw [hx]
  exact (Subgroup.normalizer (P : Set G)).mul_mem (Subgroup.le_normalizer hy)
    (Subgroup.centralizer_le_normalizer _ hz)

end InvariantPatching

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

theorem small_control_disjoint (hα : 20 ≤ Fintype.card α)
    (f g j k : TrackStar α →* H)
    (hf : SmallSupported L f) (hg : SmallSupported L g) (hj : SmallSupported L j)
    (hfj : SmallControlled c f j) (hgk : SmallControlled c g k)
    (hjk : ∀ s t, Commute (j s) (k t)) : ∀ s t, Commute (f s) (g t) := by
  have hjg (I : ControlAlphabet α) (s : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ g.range, Commute (j (universalMap (subtypeAlternatingHom I.val) s)) x :=
    small_control_transfer L c hc hd g k hg hgk I.val _ (hj I ⟨s,rfl⟩)
      (by have hh := I.property.2; omega) (fun J t => hjk _ _)
  have hfg (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ f.range, Commute (g (universalMap (subtypeAlternatingHom I.val) t)) x :=
    small_control_transfer L c hc hd f j hf hfj I.val _ (hg I ⟨t,rfl⟩)
      (by have hh := I.property.2; omega)
      (fun J s => (hjg J s _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩).symm)
  intro s
  let C := Subgroup.centralizer ({f s} : Set H)
  have hC : g.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩ y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    let J : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,
      by have hh := I.property.2; omega⟩
    exact (hfg J t _ ⟨s,rfl⟩).eq.symm
  intro t
  exact hC ⟨t,rfl⟩ (f s) (Set.mem_singleton _)

end SmallControlTransfer

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ControlledPatching
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
section ControlledPatching
variable {α H ι : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem controlled_cell_normalizes (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (hα : 20 ≤ Fintype.card α)
    (F p v : ι → TrackStar α →* H) (j k : TrackStar α →* H)
    (hp : ∀ i, SmallSupported L (p i)) (hv : ∀ i, SmallSupported L (v i))
    (hj : SmallSupported L j) (hpc : ∀ i, SmallControlled c (p i) j)
    (hvc : ∀ i, SmallControlled c (v i) k)
    (hjk : ∀ s t, Commute (j s) (k t))
    (hsplit : ∀ i s, F i s=p i s*v i s) :
    ∀ i s, F i s ∈ Subgroup.normalizer ((⨆ i, (p i).range : Subgroup H) : Set H) := by
  have hcomm (i i' : ι) (s t : TrackStar α) : Commute (p i s) (v i' t) :=
    small_control_disjoint L c hc hd hα _ _ _ _ (hp i) (hv i') hj
      (hpc i) (hvc i') hjk s t
  have ho (i : ι) (s : TrackStar α) :
      v i s ∈ Subgroup.centralizer ((⨆ i, (p i).range : Subgroup H) : Set H) := by
    have hle : (⨆ i, (p i).range : Subgroup H) ≤ Subgroup.centralizer ({v i s} : Set H) := by
      apply iSup_le
      rintro i' x ⟨t,rfl⟩ y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact (hcomm i' i t s).eq.symm
    intro x hx
    exact (hle hx _ rfl).symm
  intro i s
  exact normalizes_of_cell_split _ _ _ _ (hsplit i s)
    ((le_iSup (fun i => (p i).range) i) ⟨s,rfl⟩) (ho i s)

end ControlledPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_IndividualGridSplits
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

theorem gridPiece_control (d : D) (i : ι) :
    SmallControlled B.c (B.gridPiece hlarge Q h U W d i)
      (B.fullGeometricSector hlarge (Q i) (h i) (W d)) :=
  B.fullGeometricSector_small_control hlarge _ _ _ _ inf_le_right

theorem gridInput_split
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (d : D) (i : ι) (s : TrackStar (Fin (m+1))) :
    B.gridInput hlarge Q h U i s = B.gridPiece hlarge Q h U W d i s *
      B.gridPiece hlarge Q h U (fun d => (W d)ᶜ) d i s := by
  unfold gridInput gridPiece
  rw [← B.fullGeometricSector_union hlarge _ _ (U i ⊓ W d) (U i ⊓ (W d)ᶜ)
    (fun x y he => and_congr (hU i x y he) (hW i d x y he))
    (Set.disjoint_left.mpr (by intro x hx hy; exact hy.2 hx.2))]
  congr 2
  exact (inf_sup_left _ _ _).symm.trans (by rw [sup_compl_eq_top,inf_top_eq]) |>.symm

theorem grid_complement_coherent (i₀ i : ι) (d : D)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : B.fullGeometricSector hlarge (Q i) (h i) (W d) =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)) :
    B.fullGeometricSector hlarge (Q i) (h i) (W d)ᶜ =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)ᶜ := by
  ext s
  have hi := B.fullGeometricSector_union hlarge (Q i) (h i) (W d) (W d)ᶜ (hW i d)
    (disjoint_compl_right) s
  have h₀ := B.fullGeometricSector_union hlarge (Q i₀) (h i₀) (W d) (W d)ᶜ (hW i₀ d)
    (disjoint_compl_right) s
  rw [sup_compl_eq_top] at hi
  change B.fullGeometricSector hlarge (Q i) (h i) (wholePolygon a) s = _ at hi
  rw [B.fullGeometricSector_whole,he] at hi
  rw [sup_compl_eq_top] at h₀
  change B.fullGeometricSector hlarge (Q i₀) (h i₀) (wholePolygon a) s = _ at h₀
  rw [B.fullGeometricSector_whole] at h₀
  exact mul_left_cancel (hi.symm.trans h₀)

theorem gridInputs_normalize_oai (h20 : 20 ≤ m+1) (i₀ : ι)
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (U i).val)
    (hW : ∀ i d, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (Q i) j).val) (W d).val)
    (he : ∀ i d, B.fullGeometricSector hlarge (Q i) (h i) (W d) =
      B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)) :
    ∀ d i s, B.gridInput hlarge Q h U i s ∈
      Subgroup.normalizer ((⨆ j, (B.gridPiece hlarge Q h U W d j).range :
        Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm))) : Set _) := by
  intro d
  apply controlled_cell_normalizes _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using h20) (B.gridInput hlarge Q h U)
    (B.gridPiece hlarge Q h U W d) (B.gridPiece hlarge Q h U (fun d => (W d)ᶜ) d)
    (B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d))
    (B.fullGeometricSector hlarge (Q i₀) (h i₀) (W d)ᶜ)
  · exact B.gridPiece_supported hlarge Q h U W hU hW d
  · exact B.gridPiece_supported hlarge Q h U (fun d => (W d)ᶜ) hU
      (fun i d x y hh => not_congr (hW i d x y hh)) d
  · exact B.fullGeometricSector_supported hlarge _ _ _ (hW i₀ d)
  · intro i
    rw [← he i d]
    exact B.gridPiece_control hlarge Q h U W d i
  · intro i
    rw [← B.grid_complement_coherent hlarge Q h W i₀ i d hW (he i d)]
    exact B.gridPiece_control hlarge Q h U (fun d => (W d)ᶜ) d i
  · exact B.fullGeometricSector_commute hlarge _ _ _ _ (hW i₀ d) disjoint_compl_right
  · exact B.gridInput_split hlarge Q h U W hU hW d

end InitialCoverSystem
end IndividualGridSplits

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.gridInputs_normalize_oai.{u_1, u_2, u_3} := @OAI.SimpleAmenable.InitialCoverSystem.gridInputs_normalize_oai.{u_1, u_2, u_3}
