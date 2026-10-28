-- Prove2me | solution 1 for OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:51:47.914897+00:00
-- url     : https://prove2.me/submissions/22c901ac-0ed6-450a-851c-f52a9d213bdc

import Mathlib
import Definitions.Def_OAIQ65Sa012
import Definitions.Def_OAIQ65Sa013
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_growth_axis_law
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_pair_formal_quotient
import Theorems.Thm_OAI_SimpleAmenable_coordinateWindowLaw_eventually
import Theorems.Thm_OAI_SimpleAmenable_tangentChartTables_eventually

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonAction

private theorem exists_in_interval_avoiding (l r : ℝ) (hlr : l < r)
    (S : Set ℝ) (hS : S.Countable) : ∃ x ∈ Set.Ioo l r, x ∉ S := by
  apply Set.not_subset.mp
  intro h
  have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono h)
  linarith

theorem generic_rectangle (a : ℕ) (l₁ r₁ l₂ r₂ : ℝ)
    (hl₁ : 0 ≤ l₁) (hr₁ : r₁ ≤ 1) (h₁ : l₁ < r₁)
    (hl₂ : 0 ≤ l₂) (hr₂ : r₂ ≤ 1) (h₂ : l₂ < r₂) :
    ∃ p : GenericSquare a, p.val.1 ∈ Set.Ioo l₁ r₁ ∧ p.val.2 ∈ Set.Ioo l₂ r₂ := by
  obtain ⟨x, hx, hx'⟩ := exists_in_interval_avoiding l₁ r₁ h₁
    (Set.range ordinary) (Set.countable_range ordinary)
  let t := Real.goldenRatio ^ a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z + t*x) ∪
    Set.range (fun z : CutRing => (x - ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y, hy, hy'⟩ := exists_in_interval_avoiding l₂ r₂ h₂ S hS
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact hx' ⟨z, by simpa [cutForm] using hz.symm⟩
    · apply hy'
      exact Or.inl (Or.inl ⟨z, by simpa [cutForm] using hz.symm⟩)
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z, ?_⟩
      change ordinary z + t*x = y
      change y - t*x = ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z, ?_⟩
      apply (div_eq_iff ht).mpr
      change x - t*y = ordinary z at hz
      linarith
  exact ⟨⟨(x,y), ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩, hav⟩, hx, hy⟩

instance instNonemptyGenericSquare (a : ℕ) : Nonempty (GenericSquare a) := by
  obtain ⟨p, _⟩ := generic_rectangle a 0 1 0 1 le_rfl le_rfl zero_lt_one le_rfl le_rfl zero_lt_one
  exact ⟨p⟩

end PolygonAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem halfPlane_isClopen (a : ℕ) (j : Fin 4) (c : CutRing) :
    IsClopen (halfPlane a j c) := by
  have hc : Continuous (fun p : GenericSquare a => cutForm a j p.val) :=
    (cutForm_continuous a j).comp continuous_subtype_val
  have hopen : IsOpen (halfPlane a j c) := isOpen_lt hc continuous_const
  have he : (halfPlane a j c)ᶜ = {p : GenericSquare a | ordinary c < cutForm a j p.val} := by
    ext p
    simp only [Set.mem_compl_iff, halfPlane, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (p.property.2.2 j c).symm, le_of_lt⟩
  exact ⟨isOpen_compl_iff.mp (he ▸ isOpen_lt continuous_const hc), hopen⟩

theorem polygon_isClopen {a : ℕ} (U : polygonAlgebra a) : IsClopen U.val := by
  apply polygon_induction (P := IsClopen) (fun j c => halfPlane_isClopen a j c)
    isClopen_empty (fun _ _ h k => h.union k) (fun _ h => h.compl) U.property

theorem polygon_contains_rectangle {a : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) :
    ∃ l r : CutRing × CutRing,
      0 < ordinary l.1 ∧ ordinary l.1 < ordinary r.1 ∧ ordinary r.1 < 1 ∧
      0 < ordinary l.2 ∧ ordinary l.2 < ordinary r.2 ∧ ordinary r.2 < 1 ∧
      ∀ p : GenericSquare a,
        (ordinary l.1 < p.val.1 ∧ p.val.1 < ordinary r.1) →
        (ordinary l.2 < p.val.2 ∧ p.val.2 < ordinary r.2) → p ∈ U.val := by
  obtain ⟨p,hp⟩ := hU
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (polygon_isClopen U).isOpen p hp
  have hp0 := generic_coordinates_pos p
  obtain ⟨l₁,hl₁,hlp⟩ := exists_cut_between
    (show max 0 (p.val.1-ε) < p.val.1 by exact max_lt hp0.1 (sub_lt_self _ hε))
  obtain ⟨l₂,hl₂,hlq⟩ := exists_cut_between
    (show max 0 (p.val.2-ε) < p.val.2 by exact max_lt hp0.2 (sub_lt_self _ hε))
  obtain ⟨r₁,hpr,hr₁⟩ := exists_cut_between
    (show p.val.1 < min 1 (p.val.1+ε) by exact lt_min p.property.1.2 (lt_add_of_pos_right _ hε))
  obtain ⟨r₂,hqr,hr₂⟩ := exists_cut_between
    (show p.val.2 < min 1 (p.val.2+ε) by exact lt_min p.property.2.1.2 (lt_add_of_pos_right _ hε))
  refine ⟨(l₁,l₂),(r₁,r₂),lt_of_le_of_lt (le_max_left _ _) hl₁,
    hlp.trans hpr,(lt_min_iff.mp hr₁).1,?_,hlq.trans hqr,(lt_min_iff.mp hr₂).1,?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hl₂
  · intro q hqx hqy
    apply hball
    change max (dist q.val.1 p.val.1) (dist q.val.2 p.val.2) < ε
    rw [max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    have hx := (max_lt_iff.mp hl₁).2
    have hy := (max_lt_iff.mp hl₂).2
    have hx' := (lt_min_iff.mp hr₁).2
    have hy' := (lt_min_iff.mp hr₂).2
    constructor <;> constructor <;> linarith

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

variable {a : ℕ} {ι : Type*}

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

theorem geometricSector_input (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (i : ι) :
    B.geometricSector I b hb P h (primitiveTests (a := a) (r := r) P i) =
      (B.primitiveCopy I b hb (P i)).comp (universalProjection (alternatingGroup I)) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h _ s
  · rintro x ⟨s,rfl⟩
    rw [copyFamilyEval_range]
    exact (le_iSup (fun z => (B.primitiveFamily I b hb P z).range) (some i))
      ⟨universalProjection (alternatingGroup I) s,rfl⟩
  · rw [B.geometricSector_projection I b hb P h _ (resolved_test _ i)]
    rw [← MonoidHom.comp_assoc,B.primitiveCopy_projection]
    rfl

end InitialCoverSystem
end ActualSectorControl

section AlphabetInclusion

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveFamily_range_inclusion {ι : Type*} {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (copyFamilyEval (B.primitiveFamily J c hc P)).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i x hx
  obtain ⟨s,rfl⟩ := hx
  apply le_iSup (fun z => (B.primitiveFamily J c hc P z).range) i
  exact ⟨subalphabetHom hIJ s,DFunLike.congr_fun (B.primitiveFamily_inclusion hIJ b c hb hc P i) s⟩

end InitialCoverSystem
end AlphabetInclusion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ArithmeticTangentBasis
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ArithmeticTangentBasis

theorem cutTau_inverse_mul : (cutTau-1)*cutTau = 1 := by
  apply ordinary_injective
  simp only [map_mul,map_sub,map_one,ordinary_cutTau]
  nlinarith [Real.goldenRatio_sq]

theorem exists_short_tangent_basis (l : CutRing) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u v : CutRing, u*v = 1 ∧
      (1+|ordinary l|)*(|ordinary u|+|ordinary (cutTau*u)|) < δ := by
  have hsmall : Real.goldenRatio-1 < 1 := by linarith [Real.goldenRatio_lt_two]
  have hpos : 0 < Real.goldenRatio-1 := by linarith [Real.one_lt_goldenRatio]
  have hk : 0 < 3*(1+|ordinary l|) := by positivity
  obtain ⟨b,hb⟩ := exists_pow_lt_of_lt_one (div_pos hδ hk) hsmall
  refine ⟨(cutTau-1)^b,cutTau^b,?_,?_⟩
  · rw [← mul_pow,cutTau_inverse_mul,one_pow]
  · simp only [map_pow,map_sub,map_one,map_mul,ordinary_cutTau,abs_mul,
      abs_pow,abs_of_pos Real.goldenRatio_pos,abs_of_pos hpos]
    have hpow : 0 < (Real.goldenRatio-1)^b := pow_pos hpos b
    have hb' := (lt_div_iff₀ hk).mp hb
    nlinarith [Real.goldenRatio_lt_two,abs_nonneg (ordinary l),
      mul_pos (by positivity : 0 < 1+|ordinary l|) hpow]

end ArithmeticTangentBasis

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

section ChartTransforms

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_shared_primitive (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (i : ι) (j : κ) (he : P i = Q j)
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun _ : Unit => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.fullGeometricSector hlarge P h V = B.fullGeometricSector hlarge Q g V := by
  let S : Unit → Fin 5 × (CutRing × CutRing) := fun _ => P i
  have hS : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb S :=
    fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb P (h I hI b hb) (fun _ => i)
  rw [← B.fullGeometricSector_subfamily hlarge P S (fun _ => i) rfl h hS V hV]
  apply B.fullGeometricSector_subfamily hlarge Q S (fun _ => j) _ g hS V hV
  exact funext (fun _ => he.symm)

end InitialCoverSystem
end ChartTransforms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricCharts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SymmetricCharts

theorem exists_symmetric_short_chart (a : ℕ) (r : CutRing) (hr : 0 < ordinary r) :
    ∃ s u v : CutRing, 0 < ordinary s ∧ ordinary s < ordinary r/2 ∧ u*v=1 ∧
      (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4 := by
  obtain ⟨s,hs,hs'⟩ := exists_cut_between (by linarith : (0:ℝ) < ordinary r/2)
  obtain ⟨u,v,huv,hshort⟩ := exists_short_tangent_basis (cutTau^a) (by linarith : 0 < ordinary s/4)
  exact ⟨s,u,v,hs,hs',huv,hshort⟩

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

section AxisCoherence

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

@[simp] theorem fullGeometricSector_bot {ι : Type*} [Finite ι] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    B.fullGeometricSector hlarge P h ⊥ = 1 := by
  unfold fullGeometricSector
  have he : resolvedPolygonMask (primitiveTests (a := a) (r := r) P) (⊥ : polygonAlgebra a).val = ∅ := by
    ext ω
    simp [resolvedPolygonMask]
  rw [he,ActualLawfulTable.sector_empty]

@[simp] theorem axisSector_self (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u : CutRing) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u u) = 1 := by
  rw [coordinateInterval_self]
  exact B.fullGeometricSector_bot hlarge _ _

end InitialCoverSystem
end AxisCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisCutSequences
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section AxisCutSequences

namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

@[simp] theorem prefix_zero : D.prefixCopy B hlarge g d 0 = 1 := by
  simp only [prefixCopy,index_zero,InitialCoverSystem.axisSector_self]

end AxisCutSequence
end AxisCutSequences

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section GrowthGeneration
attribute [local instance] cutOrdinaryOrder

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem primitiveFamily_range_full_all {ι : Type*} (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  classical
  let J : Finset (Fin (m+1)) := Finset.univ.erase b
  have hIJ : I ⊆ J := by intro x hx; exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hb hx,Finset.mem_univ _⟩
  have hJ : 5 ≤ J.card := by simp [J]; omega
  have hbJ : b ∉ J := Finset.notMem_erase _ _
  exact (B.primitiveFamily_range_inclusion hIJ b b hb hbJ P).trans
    (B.primitiveFamily_range_full hlarge P J hJ b hbJ)

end InitialCoverSystem
end GrowthGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthAxisUniform
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

section PairSectors

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem primitivePair_left_resolved (i j : ι) :
    ResolvedBy (fun b => (primitiveTests (a := a) (r := r) (primitivePair P i j) b).val)
      (primitiveTests (a := a) (r := r) P i).val :=
  resolved_test _ false

end InitialCoverSystem
end PairSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section PairControl
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] in

theorem pairStar_small (I : FiveAlphabet (Fin (m+1))) (j : Option ι) :
    (B.pairStar hlarge P h j).comp (universalMap (subtypeAlternatingHom I.val)) =
      (B.smallPrimitiveInputs hlarge P I j).comp
        (universalProjection (alternatingGroup I.val)) := by
  cases j with
  | none =>
    change (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))).comp _ =
      (B.initialAlphabet I.val 0).comp _
    rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,B.initialAlphabet_zero]
  | some i =>
    let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
    have hb := smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)
    change (B.fullGeometricSector hlarge (primitivePair P i i) (h i i)
      (primitiveTests (a := a) (r := r) P i)).comp _ = _
    rw [B.fullGeometricSector_inclusion hlarge _ _ I.val (by rw [I.property.2]) b hb
      (h i i I.val (by rw [I.property.2]; omega) b hb) _ (primitivePair_left_resolved P i i)]
    exact B.geometricSector_input I.val b hb (primitivePair P i i) (h i i _ (by rw [I.property.2]; omega) b hb) false

omit [Finite ι] in

theorem pairStar_range :
    (⨆ j, (B.pairStar hlarge P h j).range) =
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  apply le_antisymm
  · apply iSup_le
    rintro j x ⟨s,rfl⟩
    exact B.pairStar_mem hlarge P h j s
  · rw [smallFamilyEval_range]
    apply iSup_le
    intro I
    apply iSup_le
    rintro j x ⟨s,rfl⟩
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
    apply le_iSup (fun j => (B.pairStar hlarge P h j).range) j
    exact ⟨universalMap (subtypeAlternatingHom I.val) t,
      DFunLike.congr_fun (B.pairStar_small hlarge P h I j) t⟩

end InitialCoverSystem
end PairControl

section AssignmentExclusions
variable {E S G K ι Ω : Type*} [Group E] [Group S] [Group G] [Group K]

theorem formalAssignmentEval_surjective [Finite ι] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π) : Function.Surjective (formalAssignmentEval (ι := ι) π) := by
  have hv : Function.Surjective (assignmentEval (E := S) (fun i : ι => {σ : ι → Bool | σ i = true})) := by
    apply assignmentEval_surjective
    intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  have hw : Function.Surjective (copySourceMap (ι := ι) π) := by
    apply FreeGroup.map_surjective
    rintro ⟨i,s⟩
    obtain ⟨t,rfl⟩ := hπ s
    exact ⟨(i,t),rfl⟩
  exact hv.comp hw

theorem forbidden_factor_trivial [Finite ι] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π)
    (F : Option ι → E →* G) (ρ : G →* K) (c : S →* K)
    (σ : ι → Bool) (pattern : Ω → ι → Bool)
    (hforbid : σ ∉ Set.range pattern)
    (hwhole : ρ.comp (F none) = c.comp π)
    (hcomponent : ρ.comp (copyFamilyEval F) =
      c.comp ((Pi.evalMonoidHom _ σ).comp (formalAssignmentEval π)))
    (hlocal : ∀ w, ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 →
      ∀ t, Commute (copyFamilyEval F w) (F none t)) : ∀ s, c s = 1 := by
  classical
  have hcomm (s t : S) : Commute (c s) (c t) := by
    obtain ⟨w,hw⟩ := formalAssignmentEval_surjective (ι := ι) π hπ (Pi.mulSingle σ s)
    have hmodel : ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 := by
      ext ω
      change formalAssignmentEval π w (pattern ω) = 1
      rw [hw,Pi.mulSingle_eq_of_ne]
      exact fun he => hforbid ⟨ω,he⟩
    obtain ⟨v,hv⟩ := hπ t
    have hh := (hlocal w hmodel v).map ρ
    have he := DFunLike.congr_fun hcomponent w
    have ht := DFunLike.congr_fun hwhole v
    simp only [MonoidHom.comp_apply,Pi.evalMonoidHom_apply,hw,Pi.mulSingle_eq_same] at he
    simp only [MonoidHom.comp_apply,hv] at ht
    rwa [he,ht] at hh
  let : IsMulCommutative c.range := ⟨⟨fun x y => by
    obtain ⟨s,hs⟩ := x.property
    obtain ⟨t,ht⟩ := y.property
    apply Subtype.ext
    change x.val*y.val = y.val*x.val
    rw [← hs,← ht]
    exact (hcomm s t).eq⟩⟩
  intro s
  exact congrArg Subtype.val (perfect_hom_to_commGroup c.rangeRestrict s)

theorem formal_component_of_inputs (π : E →* S)
    (F : Option ι → E →* G) (ρ : G →* K) (c : S →* K) (σ : ι → Bool)
    (hwhole : ρ.comp (F none) = c.comp π)
    (hinput : ∀ i s, ρ (F (some i) s) = if σ i then c (π s) else 1) :
    ρ.comp (copyFamilyEval F) = c.comp ((Pi.evalMonoidHom _ σ).comp (formalAssignmentEval π)) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  cases i with
  | none => simpa only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily,sectorMask_of_mem _ _ _ (Set.mem_univ _),
      Pi.evalMonoidHom_apply] using DFunLike.congr_fun hwhole s
  | some i =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily,Pi.evalMonoidHom_apply]
    cases hs : σ i <;> simp [sectorMask,hinput,hs]

end AssignmentExclusions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
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
section FormalCoordinates
variable {S Q Ω : Type*} [Group S] [Group Q] [DecidableEq Ω]

theorem coordinateProjection_apply (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ)
    (hz : Subgroup.center Q = ⊥) (ω : Ω) (s : Ω → S) :
    coordinateProjection φ hφ hz ω (φ s) = φ (Pi.mulSingle ω (s ω)) := by
  classical
  have he : s = Pi.mulSingle ω (s ω)*assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} s := by
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]
  change (coordinateFactors φ hφ ω).projectLeft hz (φ s) = _
  conv_lhs => rw [he,map_mul]
  exact (coordinateFactors φ hφ ω).projectLeft_factors hz ⟨s ω,rfl⟩ ⟨s,rfl⟩

theorem formalMap_kill_of_actual [Finite Ω]
    (φ : (Ω → S) →* Q) (U : Set Ω)
    (hexcluded : ∀ ω, ω ∉ U → ∀ s, φ (Pi.mulSingle ω s) = 1)
    (f : Ω → S) (hf : ∀ ω ∈ U, f ω = 1) : φ f = 1 := by
  classical
  apply (Submonoid.pi_mem_of_mulSingle_mem (H := φ.ker) f)
  intro ω
  by_cases hω : ω ∈ U
  · change φ (Pi.mulSingle ω (f ω)) = 1
    rw [hf ω hω,Pi.mulSingle_one,map_one]
  · exact hexcluded ω hω (f ω)

end FormalCoordinates

section CodRestrictGeneration
variable {E G ι : Type*} [Group E] [Group G]

theorem codRestrict_iSup_top (F : ι → E →* G) (K : Subgroup G)
    (hm : ∀ i s, F i s ∈ K) (hgen : (⨆ i, (F i).range : Subgroup G) = K) :
    (⨆ i, (MonoidHom.codRestrict (F i) K (hm i)).range : Subgroup K) = ⊤ := by
  apply (Subgroup.map_injective K.subtype_injective)
  rw [Subgroup.map_iSup]
  have he (i : ι) : Subgroup.map K.subtype ((MonoidHom.codRestrict (F i) K (hm i)).range) = (F i).range := by
    rw [← MonoidHom.range_comp]
    rfl
  simp only [he]
  rw [hgen,← MonoidHom.range_eq_map,K.range_subtype]

end CodRestrictGeneration

section StarFormalComponents
variable {E S G ι κ Ω : Type*} [Group E] [Group S] [Group G]
    [Finite ι] [DecidableEq (ι → Bool)] [Group.IsPerfect G]
    (π : E →* S) (c : S →* G) (F : Option ι → E →* G)
    (hc : F none = c.comp π)
    (φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G))
    (hφ : Function.Surjective φ)
    (hφc : φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp c)
    (hφi : ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp π =
      (QuotientGroup.mk' _).comp (F (some i)))

include hc hφc hφi in
omit [Finite ι] [DecidableEq (ι → Bool)] [Group.IsPerfect G] in
theorem star_formal_eval : (QuotientGroup.mk' _).comp (copyFamilyEval F) =
    φ.comp (formalAssignmentEval π) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  cases i with
  | none =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily]
    rw [hc]
    exact (DFunLike.congr_fun hφc (π s)).symm
  | some i =>
    simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,maskFamily]
    exact (DFunLike.congr_fun (hφi i) s).symm

include hc hφc in
omit [Finite ι] in
theorem formalCoordinate_whole (σ : ι → Bool) :
    (formalCoordinateMap φ hφ σ).comp (F none) =
      (formalCoordinateSource φ σ).comp π := by
  ext s
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (F none s)) = _
  rw [hc]
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (c (π s))) = _
  have he := DFunLike.congr_fun hφc (π s)
  simp only [MonoidHom.comp_apply] at he
  rw [← he]
  simp [coordinateProjection_apply,formalCoordinateSource,sectorMask]

include hφi in
omit [Finite ι] in
theorem formalCoordinate_input (σ : ι → Bool) (i : ι) (s : E) :
    formalCoordinateMap φ hφ σ (F (some i) s) =
      if σ i then formalCoordinateSource φ σ (π s) else 1 := by
  change coordinateProjection φ hφ perfect_center_quotient σ ((QuotientGroup.mk' _) (F (some i) s)) = _
  have he := DFunLike.congr_fun (hφi i) s
  simp only [MonoidHom.comp_apply] at he
  rw [← he]
  simp only [coordinateProjection_apply]
  cases hs : σ i <;> simp [sectorMask,hs,formalCoordinateSource]

include hc hφ hφc hφi in
omit [Finite ι] in
theorem formal_exclusion_of_subfamily [Finite κ] [Group.IsPerfect S]
    (hπ : Function.Surjective π) (v : κ → ι) (σ : ι → Bool) (pattern : Ω → κ → Bool)
    (hbad : σ ∘ v ∉ Set.range pattern)
    (hlocal : ∀ w, ((assignmentPullback pattern).comp (formalAssignmentEval π)) w = 1 →
      ∀ t, Commute (copyFamilyEval (fun j => F (j.map v)) w) (F none t)) :
    ∀ s, φ (Pi.mulSingle σ s) = 1 := by
  apply forbidden_factor_trivial π hπ (fun j => F (j.map v))
    (formalCoordinateMap φ hφ σ) (formalCoordinateSource φ σ) (σ ∘ v) pattern hbad
  · exact formalCoordinate_whole π c F hc φ hφ hφc σ
  · apply formal_component_of_inputs π
    · exact formalCoordinate_whole π c F hc φ hφ hφc σ
    · intro i s
      exact formalCoordinate_input π F φ hφ hφi σ (v i) s
  · exact hlocal

omit [Group.IsPerfect G] in
include hc hφc hφi in
theorem formal_centralOn_of_exclusions {H : Type*} [Group H]
    (q : G →* H) (U : Set (ι → Bool))
    (hgen : Function.Surjective (copyFamilyEval F))
    (hfaith : ∀ w, q (copyFamilyEval F w) = 1 → ∀ σ ∈ U, formalAssignmentEval π w σ = 1)
    (hkill : ∀ σ, σ ∉ U → ∀ s, φ (Pi.mulSingle σ s) = 1) :
    q.ker ≤ Subgroup.center G := by
  classical
  intro x hx
  obtain ⟨w,rfl⟩ := hgen x
  apply (QuotientGroup.eq_one_iff _).mp
  have he := DFunLike.congr_fun (star_formal_eval π c F hc φ hφc hφi) w
  rw [MonoidHom.comp_apply,MonoidHom.comp_apply] at he
  change (QuotientGroup.mk' (Subgroup.center G)) (copyFamilyEval F w) = 1
  rw [he]
  exact formalMap_kill_of_actual φ U hkill _ (hfaith w hx)

end StarFormalComponents

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_StarProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualStarProjection
variable {a m : ℕ} {ι : Type*} [Finite ι]

theorem formalPolygonTable_whole (U : ι → polygonAlgebra a) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask Set.univ s) = conditionalAlternatingHom (wholePolygon a) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask Set.univ s) = sectorMask Set.univ s := by
    ext ω; simp [assignmentPullback,sectorMask]
  rw [he]
  exact actualPolygonTableHom_whole U s

theorem formalPolygonTable_test (U : ι → polygonAlgebra a) (i : ι) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask {σ | σ i = true} s) = conditionalAlternatingHom (U i) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask {σ | σ i = true} s) = polygonTableInput U i s := by rfl
  rw [he]
  exact actualPolygonTableHom_input U i s

theorem formalPolygonTable_eq_one (U : ι → polygonAlgebra a)
    (f : (ι → Bool) → alternatingGroup (Fin (m+1))) (h : formalPolygonTable U f = 1)
    (σ : ι → Bool) (hσ : σ ∈ Set.range (polygonAssignment U)) : f σ = 1 := by
  have he := actualPolygonTableHom_injective U (h.trans (map_one _).symm)
  exact congrFun he ⟨σ,hσ⟩

variable {E H : Type*} [Group E] [Group H]

theorem actualStar_eval_projection (π : E →* alternatingGroup (Fin (m+1)))
    (U : ι → polygonAlgebra a) (F : Option ι → E →* H)
    (q : H →* polygonAlternatingGroup a (m+1))
    (hq : ∀ j, q.comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp π) :
    q.comp (copyFamilyEval F) = (formalPolygonTable U).comp (formalAssignmentEval π) := by
  apply FreeGroup.ext_hom
  rintro ⟨j,s⟩
  simp only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
    FreeGroup.map.of,assignmentEval]
  have he := DFunLike.congr_fun (hq j) s
  simp only [MonoidHom.comp_apply] at he
  rw [he]
  cases j with
  | none => exact (formalPolygonTable_whole U (π s)).symm
  | some i => exact (formalPolygonTable_test U i (π s)).symm

end ActualStarProjection

section PairProjection
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] in
theorem pairStar_projection (j : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.pairStar hlarge P h j) =
      (conditionalAlternatingHom (primitiveFamilyTests (a := a) (r := r) P j)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) := by
  cases j with
  | none =>
    change (coverMap _ _).comp (B.c.comp _) = _
    rw [← MonoidHom.comp_assoc,B.c_projection]
    rfl
  | some i =>
    exact B.fullGeometricSector_projection hlarge _ _ _ (primitivePair_left_resolved P i i)

omit [Finite ι] in

theorem pairStar_subfamily_mem (v : κ → ι)
    (hp : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (j : Option κ) (s : TrackStar (Fin (m+1))) :
    B.pairStar hlarge P h (j.map v) s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range := by
  cases j with
  | none => exact B.constant_range_full hlarge (P ∘ v) ⟨_,rfl⟩
  | some j =>
    change B.fullGeometricSector hlarge (primitivePair P (v j) (v j)) (h (v j) (v j))
      (primitiveTests (a := a) (r := r) (primitivePair P (v j) (v j)) false) s ∈ _
    rw [B.fullGeometricSector_shared_primitive hlarge (primitivePair P (v j) (v j)) (P ∘ v)
      false j rfl _ hp _ (resolved_test _ ())]
    exact B.fullGeometricSector_mem hlarge _ hp _ s

end InitialCoverSystem
end PairProjection

section PairExclusionLocal
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

omit [Finite ι] in
theorem pairStar_subfamily_local (v : κ → ι)
    (hp : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (w : FreeGroup (Option κ × TrackStar (Fin (m+1))))
    (hw : ((assignmentPullback (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)))).comp
      (formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))))) w = 1)
    (s : TrackStar (Fin (m+1))) :
    Commute (copyFamilyEval (fun j => B.pairStar hlarge P h (j.map v)) w)
      (B.pairStar hlarge P h none s) := by
  let U := primitiveTests (a := a) (r := r) (P ∘ v)
  let F := fun j : Option κ => B.pairStar hlarge P h (j.map v)
  have hproj j : (coverMap M (alternatingGenerator a r m hm)).comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp
        (universalProjection (alternatingGroup (Fin (m+1)))) := by
    rw [show F j = B.pairStar hlarge P h (j.map v) from rfl,B.pairStar_projection]
    cases j <;> rfl
  have he := DFunLike.congr_fun (actualStar_eval_projection
    (universalProjection (alternatingGroup (Fin (m+1)))) U F _ hproj) w
  simp only [MonoidHom.comp_apply] at he
  have hz : (coverMap M (alternatingGenerator a r m hm)) (copyFamilyEval F w) = 1 := by
    rw [he]
    change actualPolygonTableHom U _ = 1
    have hz : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
        (formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))) w) = 1 := by
      funext ω
      obtain ⟨p,hp⟩ := ω.property
      have he := congrFun hw p
      change formalAssignmentEval (universalProjection (alternatingGroup (Fin (m+1)))) w
        (polygonAssignment U p) = 1 at he
      simpa only [assignmentPullback,MonoidHom.coe_mk,OneHom.coe_mk,Function.comp_apply,hp,Pi.one_apply] using he
    rw [hz,map_one]
  have hm : (copyFamilyEval F).range ≤ (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range := by
    rw [copyFamilyEval_range]
    apply iSup_le
    rintro j x ⟨t,rfl⟩
    exact B.pairStar_subfamily_mem hlarge P h v hp j t
  exact (centralOn_iff _ _).mp (B.fullPrimitiveFamily_central hlarge (P ∘ v) hp)
    _ (hm ⟨w,rfl⟩) hz _ (B.constant_range_full hlarge (P ∘ v) ⟨_,rfl⟩)

end InitialCoverSystem
end PairExclusionLocal

section PairActualLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ D : Type*} [Fintype ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ i j I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (primitivePair P i j))

include h in

theorem pair_actual_central (h20 : 20 ≤ m+1) (v : D → κ → ι)
    (hp : ∀ d I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v d))
    (hexclude : ∀ σ : ι → Bool,
      σ ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) →
      ∃ d, σ ∘ v d ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d)))) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  classical
  let K := (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
  let : Group.IsPerfect K := smallFamilyEval_perfect _
  let π := universalProjection (alternatingGroup (Fin (m+1)))
  let F := B.pairCarrierStar hlarge P h
  let c := B.pairCarrierConstant hlarge P
  let q := (coverMap M (alternatingGenerator a r m hm)).comp K.subtype
  let U := primitiveTests (a := a) (r := r) P
  obtain ⟨φ,hφ,hφc,hφi⟩ := B.pair_formal_quotient hlarge P h h20
  have hF : F none = c.comp π := rfl
  have hgen : Function.Surjective (copyFamilyEval F) := by
    apply MonoidHom.range_eq_top.mp
    rw [copyFamilyEval_range]
    exact codRestrict_iSup_top _ _ (B.pairStar_mem hlarge P h) (B.pairStar_range hlarge P h)
  have hproj j : q.comp (F j) =
      (conditionalAlternatingHom (match j with | none => wholePolygon a | some i => U i)).comp π := by
    change (coverMap _ _).comp (B.pairStar hlarge P h j) = _
    rw [B.pairStar_projection]
    cases j <;> rfl
  have heval := actualStar_eval_projection π U F q hproj
  apply formal_centralOn_of_exclusions π c F hF φ hφc hφi q
    (Set.range (polygonAssignment U)) hgen
  · intro w hw σ hσ
    have he := DFunLike.congr_fun heval w
    simp only [MonoidHom.comp_apply] at he
    exact formalPolygonTable_eq_one U _ (he.symm.trans hw) σ hσ
  · intro σ hσ
    obtain ⟨d,hd⟩ := hexclude σ hσ
    apply formal_exclusion_of_subfamily π c F hF φ hφ hφc hφi
      (universalProjection_surjective _) (v d) σ
      (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d))) hd
    intro w hw t
    apply Subtype.ext
    have he := DFunLike.congr_fun (copyFamilyEval_comp (fun j => F (j.map (v d))) K.subtype) w
    change copyFamilyEval (fun j => B.pairStar hlarge P h (j.map (v d))) w =
      (copyFamilyEval (fun j => F (j.map (v d))) w).val at he
    change (copyFamilyEval (fun j => F (j.map (v d))) w).val * B.pairStar hlarge P h none t =
      B.pairStar hlarge P h none t * (copyFamilyEval (fun j => F (j.map (v d))) w).val
    rw [← he]
    exact (B.pairStar_subfamily_local hlarge P h (v d) (hp d) w hw t).eq

include hlarge h in

theorem pair_actual_law (h20 : 20 ≤ m+1) (v : D → κ → ι)
    (hp : ∀ d I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v d))
    (hexclude : ∀ σ : ι → Bool,
      σ ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) →
      ∃ d, σ ∘ v d ∉ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v d))))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) : B.PrimitiveFamilyLaw I b hb P :=
  (B.pair_actual_central hlarge P h h20 v hp hexclude).mono
    (B.primitiveFamily_range_full_all hlarge P I b hb)

end InitialCoverSystem
end PairActualLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateProductPatterns
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CoordinateProductPatterns

theorem generic_fixed_x {a : ℕ} (p : GenericSquare a) (l r : ℝ)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l < r) :
    ∃ q : GenericSquare a, q.val.1 = p.val.1 ∧ q.val.2 ∈ Set.Ioo l r := by
  let x := p.val.1
  let t := Real.goldenRatio^a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z+t*x) ∪
    Set.range (fun z : CutRing => (x-ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y,hy,hy'⟩ : ∃ y ∈ Set.Ioo l r, y ∉ S := by
    apply Set.not_subset.mp
    intro hh
    have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono hh)
    linarith
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact p.property.2.2 0 z hz
    · exact hy' (Or.inl (Or.inl ⟨z,by simpa [cutForm] using hz.symm⟩))
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z,?_⟩
      change ordinary z+t*x=y
      change y-t*x=ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z,?_⟩
      apply (div_eq_iff ht).mpr
      change x-t*y=ordinary z at hz
      linarith
  exact ⟨⟨(x,y),p.property.1,⟨by linarith [hy.1],by linarith [hy.2]⟩,hav⟩,rfl,hy⟩

theorem generic_fixed_y {a : ℕ} (p : GenericSquare a) (l r : ℝ)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hlr : l < r) :
    ∃ q : GenericSquare a, q.val.2 = p.val.2 ∧ q.val.1 ∈ Set.Ioo l r := by
  obtain ⟨q,hq,hqr⟩ := generic_fixed_x (genericSwap p) l r hl hr hlr
  exact ⟨genericSwap q,hq,hqr⟩

theorem coordinate_patterns_product {a : ℕ} {ι : Type*} [Finite ι]
    (U : Fin 2 × ι → polygonAlgebra a)
    (hcoord : ∀ j i (p q : GenericSquare a), coordinate j p = coordinate j q →
      (p ∈ (U (j,i)).val ↔ q ∈ (U (j,i)).val))
    (σ : Fin 2 × ι → Bool)
    (hσ : ∀ j : Fin 2, (fun i => σ (j,i)) ∈ Set.range (polygonAssignment (fun i => U (j,i)))) :
    σ ∈ Set.range (polygonAssignment U) := by
  classical
  let V : Fin 2 → polygonAlgebra a := fun j =>
    ⟨{q | polygonAssignment (fun i => U (j,i)) q = fun i => σ (j,i)},
      polygonAssignment_fiber_mem _ _⟩
  have hV (j : Fin 2) : (V j).val.Nonempty := hσ j
  obtain ⟨l₀,r₀,hl₀,hlr₀,hr₀,hl₀',hlr₀',hr₀',hbox₀⟩ := polygon_contains_rectangle (V 0) (hV 0)
  obtain ⟨l₁,r₁,hl₁,hlr₁,hr₁,hl₁',hlr₁',hr₁',hbox₁⟩ := polygon_contains_rectangle (V 1) (hV 1)
  obtain ⟨p,hpx,hpy⟩ := generic_rectangle a (ordinary l₀.1) (ordinary r₀.1)
    (ordinary l₁.2) (ordinary r₁.2) hl₀.le hr₀.le hlr₀ hl₁'.le hr₁'.le hlr₁'
  obtain ⟨q₀,hq₀,hq₀y⟩ := generic_fixed_x p (ordinary l₀.2) (ordinary r₀.2) hl₀'.le hr₀'.le hlr₀'
  obtain ⟨q₁,hq₁,hq₁x⟩ := generic_fixed_y p (ordinary l₁.1) (ordinary r₁.1) hl₁.le hr₁.le hlr₁
  have hq₀mem := hbox₀ q₀ (by rwa [hq₀]) hq₀y
  have hq₁mem := hbox₁ q₁ hq₁x (by rwa [hq₁])
  refine ⟨p,?_⟩
  funext ⟨j,i⟩
  fin_cases j
  · have he := congrFun hq₀mem i
    change decide (p ∈ (U (0,i)).val) = _
    change decide (q₀ ∈ (U (0,i)).val) = _ at he
    rw [decide_eq_decide.mpr (hcoord 0 i p q₀ hq₀.symm)]
    exact he
  · have he := congrFun hq₁mem i
    change decide (p ∈ (U (1,i)).val) = _
    change decide (q₁ ∈ (U (1,i)).val) = _ at he
    rw [decide_eq_decide.mpr (hcoord 1 i p q₁ hq₁.symm)]
    exact he

end CoordinateProductPatterns

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoordinateJointLaw
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CoordinateJointLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem coordinate_pair_law {n k : ℕ} (hn : 2 ≤ n)
    (g : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (haxis : ∀ d p I b hb, B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d k p))
    (i j : Fin 2 × Fin (k-1)) (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (primitivePair (coordinateWindowPrimitives k q) i j) := by
  classical
  by_cases hij : i.1 = j.1
  · have h := PrimitiveFamilyLaw.reindex B I b hb (axisWindowPrimitives i.1 k (q i.1))
      (haxis i.1 (q i.1) I b hb) (fun t : Bool => if t then j.2 else i.2)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    cases t <;> simp [primitivePair,axisWindowPrimitives,coordinateWindowPrimitives,hij]
  · let p : Fin 2 → ℤ := fun d => if d=i.1 then q i.1+(i.2.val:ℤ) else q j.1+(j.2.val:ℤ)
    let v : Bool → Fin 2 × Fin (n-1) := fun t => (if t then j.1 else i.1,⟨0,by omega⟩)
    have h := PrimitiveFamilyLaw.reindex B I b hb (coordinateWindowPrimitives n p) (g I b hb p) v
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    cases t <;> simp [primitivePair,coordinateWindowPrimitives,p,v,Ne.symm hij]

omit B in
theorem coordinateWindowPatterns {k : ℕ} (q : Fin 2 → ℤ)
    (σ : Fin 2 × Fin (k-1) → Bool)
    (hσ : ∀ d : Fin 2, (fun i => σ (d,i)) ∈
      Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (axisWindowPrimitives d k (q d))))) :
    σ ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives k q))) := by
  apply coordinate_patterns_product _ _ σ hσ
  intro d i p p' hp
  simp only [primitiveTests,primitiveFamilyTests,coordinateWindowPrimitives,initialTest_coordinate]
  fin_cases d <;>
    simp_all [spatialTranslate,coordinatePrimitive,coordinateShift,halfPlane,cutForm,translate_val,coordinate]

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_joint_law (h20 : 20 ≤ m+1) {n k : ℕ} (hn : 2 ≤ n)
    (g : B.CoordinateWindowLaw n)
    (haxis : ∀ d p I b hb, B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d k p)) :
    B.CoordinateWindowLaw k := by
  classical
  intro I b hb q
  apply B.pair_actual_law (by omega) (coordinateWindowPrimitives k q)
    (fun i j I _ b hb => B.coordinate_pair_law hn g q haxis i j I b hb) h20
    (fun d : Fin 2 => fun i : Fin (k-1) => (d,i)) _ _ I b hb
  · intro d I _ b hb
    exact haxis d (q d) I b hb
  · intro σ hσ
    by_contra! h
    apply hσ
    apply coordinateWindowPatterns q σ
    exact h

end InitialCoverSystem
end CoordinateJointLaw

section CoordinatePropagation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_growth (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → B.CoordinateWindowLaw n → B.CoordinateWindowLaw (growthNewLength n) := by
  obtain ⟨N,hN,h⟩ := growth_axis_law (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  refine ⟨N,hN,?_⟩
  intro M B hB n hn g
  exact B.coordinate_joint_law hlarge (by omega) g (h M B hB n hn g)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem coordinate_iteration {M : ℕ} (B : InitialCoverSystem a r m hm M)
    (N : ℕ) (hN : 5 ≤ N) (hbase : B.CoordinateWindowLaw N)
    (hstep : ∀ n, N ≤ n → B.CoordinateWindowLaw n → B.CoordinateWindowLaw (growthNewLength n)) :
    ∀ n, B.CoordinateWindowLaw n := by
  have hge : ∀ n, N ≤ n → B.CoordinateWindowLaw n := by
    apply Nat.le_induction
    · exact hbase
    · intro n hn g
      apply (hstep n hn g).mono B
      simp only [growthNewLength]
      omega
  intro n
  rcases le_total n N with hn|hn
  · exact hbase.mono B hn
  · exact hge n hn

end InitialCoverSystem
end CoordinatePropagation

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RectangularBound
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section RectangularBound
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_all_eventually (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ n, B.CoordinateWindowLaw n := by
  obtain ⟨s,w,z,hs,hsr,hwz,hshort⟩ := exists_symmetric_short_chart a r hr.1
  obtain ⟨N,hN,hstep⟩ := InitialCoverSystem.coordinate_growth (hm := hm) hlarge hr
    s w z hs hsr hwz hshort (show (1000:ℝ) ≤ 1000 from le_rfl)
    (by convert hSlope using 1; norm_num) hconj
  obtain ⟨L₁,hL₁⟩ := coordinateWindowLaw_eventually (a := a) (hm := hm) hr (by omega) N
  obtain ⟨L₂,hL₂⟩ := tangentChartTables_eventually (a := a) (hm := hm) hr (by omega)
    (symmetricWindowLength s) (symmetricWindowStart s) w
  refine ⟨L₁+L₂,?_⟩
  intro M hM B
  apply B.coordinate_iteration N (by omega) (hL₁ M (by omega) B)
  intro n hn g
  exact hstep M B (fun d e z I _ b hb => hL₂ M (by omega) B d e z I b hb) n hn g

end RectangularBound

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

section FullTangentOverlap

theorem exists_full_overlap_window (a : ℕ) (r u : CutRing) :
    ∃ k : ℕ, ∃ p : Fin 2 → ℤ, ∀ d : Fin 2, ∀ e : Fin 5, ∀ j : Fin 2,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) := by
  let q (i : Fin 2 × Fin 5 × Bool) (j : Fin 2) : ℤ :=
    endpointLabel (if i.2.2 then clippingOverlapUpper r (tangentOffset a i.1 (signedShortSteps u i.2.1)) j
      else clippingOverlapLower r (tangentOffset a i.1 (signedShortSteps u i.2.1)) j)
  obtain ⟨k,p,hp⟩ := finite_coordinate_windows_container (fun _ : Fin 2 × Fin 5 × Bool => 1) q
  refine ⟨k,p,fun d e j => ?_⟩
  have hL := hp (d,e,false) j
  have hU := hp (d,e,true) j
  dsimp [q] at hL hU
  omega

end FullTangentOverlap

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FinePatchAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section FinePatchAtlas

theorem rectangularAtlas_fixed_radius_eventually_oai {a m : ℕ} {r : CutRing} {hm : 2  ≤  m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (hlarge : 20  ≤  m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hSlope : 8000 < ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ s : CutRing, 0 < ordinary s ∧ ordinary s < ordinary r/8 ∧
      ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
        ∃ A : B.RectangularAtlas, A.radius=s := by
  obtain ⟨s,u,v,hs,hsr,huv,hshort⟩ := exists_symmetric_short_chart a r hr.1
  obtain ⟨k,p,hp⟩ := exists_full_overlap_window a r u
  obtain ⟨s₁,hs₁,hs₁'⟩ := exists_cut_between (by linarith : (0:ℝ) < ordinary r/8)
  obtain ⟨L₁,hL₁⟩ := coordinate_all_eventually (hm := hm) hlarge hr hSlope hconj
  obtain ⟨L₂,hL₂⟩ := tangentChartTables_eventually (hm := hm) hr (by omega) k p u
  obtain ⟨L₃,hL₃⟩ := tangentChartTables_eventually (hm := hm) hr (by omega)
    (symmetricWindowLength s₁) (symmetricWindowStart s₁) u
  refine ⟨s₁,hs₁,hs₁',L₁+L₂+L₃,fun M hM B => ?_⟩
  refine ⟨⟨k,p,u,v,huv,?_,hp,hL₁ M (by omega) B,?_,s₁,hs₁,hs₁',?_⟩,rfl⟩
  · nlinarith
  · intro d e z I _ b hb
    exact hL₂ M (by omega) B d e z I b hb
  · intro d e z I _ b hb
    exact hL₃ M (by omega) B d e z I b hb

end FinePatchAtlas

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually_oai := @OAI.SimpleAmenable.rectangularAtlas_fixed_radius_eventually_oai
