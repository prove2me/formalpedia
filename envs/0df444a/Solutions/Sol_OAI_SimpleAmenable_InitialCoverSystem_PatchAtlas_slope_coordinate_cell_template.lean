-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:01:35.304334+00:00
-- url     : https://prove2.me/submissions/6e13a260-a510-4f48-b2f7-66dde8249ce1

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_crossing_cell_actions
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_all_rectangle_control_to_template
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ResolvedBoolean
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section FiniteCoordinateAlgebra

theorem coordinate_window_between_resolved {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (i k : ℕ) (hik : i ≤ k) (hk : k < n) :
    coordinateBetween a j (((q j+(i:ℤ)):CutRing)*cutTau)
      (((q j+(k:ℤ)):CutRing)*cutTau) ∈
      resolvedAlgebra (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) z).val) := by
  let B := resolvedAlgebra (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
    (coordinateWindowPrimitives n q) z).val)
  have hp := coordinate_prefix_generated B j (((q j+(i:ℤ)):CutRing)*cutTau) (k-i)
  have he : (((q j+(i:ℤ)):CutRing)*cutTau) + ((k-i:ℕ):CutRing)*cutTau =
      (((q j+(k:ℤ)):CutRing)*cutTau) := by
    push_cast
    rw [Nat.cast_sub hik]
    ring
  rw [he] at hp
  apply hp
  intro t ht
  have ht' : i+t < n-1 := by omega
  have hh := resolved_test (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) z).val) (j,⟨i+t,ht'⟩)
  change (spatialTranslate (coordinateShift j
      (((q j+((i+t:ℕ):ℤ)):CutRing)*cutTau))
      (initialTest a r (coordinateTestIndex j))).val ∈ B at hh
  rw [initialTest_coordinate] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  push_cast
  ring

end FiniteCoordinateAlgebra

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowIntervals
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowIntervals

theorem coordinate_window_between_resolved_all {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (i k : ℕ) (hi : i < n) (hk : k < n) :
    coordinateBetween a j (((q j+(i:ℤ)):CutRing)*cutTau)
      (((q j+(k:ℤ)):CutRing)*cutTau) ∈ resolvedAlgebra
        (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
          (coordinateWindowPrimitives n q) z).val) := by
  by_cases hik : i ≤ k
  · exact coordinate_window_between_resolved n q j i k hik hk
  · let u : CutRing := ((q j+(i:ℤ)):CutRing)*cutTau
    let v : CutRing := ((q j+(k:ℤ)):CutRing)*cutTau
    by_cases h : Int.fract (ordinary (v-u)) = 0
    · rw [coordinateBetween_empty j u v h]
      exact BooleanSubalgebra.bot_mem
    · have hr := coordinateBetween_reverse (a := a) j u v h
      have hh := coordinate_window_between_resolved (a := a) (r := r) n q j k i (by omega) hi
      rw [hr] at hh
      simpa only [compl_compl] using BooleanSubalgebra.compl_mem hh

theorem coordinateLabelWindow_resolved {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (u v : CutRing)
    (hu : q j ≤ endpointLabel u ∧ endpointLabel u < q j+n)
    (hv : q j ≤ endpointLabel v ∧ endpointLabel v < q j+n) :
    coordinateBetween a j u v ∈ resolvedAlgebra
      (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) z).val) := by
  let i := (endpointLabel u-q j).toNat
  let k := (endpointLabel v-q j).toNat
  have hi : (i:ℤ) = endpointLabel u-q j := Int.toNat_of_nonneg (by omega)
  have hk : (k:ℤ) = endpointLabel v-q j := Int.toNat_of_nonneg (by omega)
  have hi' : i < n := by omega
  have hk' : k < n := by omega
  have hu' : u = (((q j+(i:ℤ)):CutRing)*cutTau)+(u.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hi,endpointLabel]
  have hv' : v = (((q j+(k:ℤ)):CutRing)*cutTau)+(v.re:CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [cutTau,hk,endpointLabel]
  rw [hu',hv',coordinateBetween_period]
  exact coordinate_window_between_resolved_all n q j i k hi' hk'

end WindowIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowSubfamilies
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section CircularIntervals

theorem coordinateInterval_window {a : ℕ} {r : CutRing}
    (n : ℕ) (q : Fin 2 → ℤ) (j : Fin 2) (u v : CutRing)
    (hu : q j ≤ endpointLabel u ∧ endpointLabel u < q j+n)
    (hv : q j ≤ endpointLabel v ∧ endpointLabel v < q j+n) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateInterval a j u v).val :=
  coordinateLabelWindow_resolved n q j u v hu hv

end CircularIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem spatialTranslate_coordinateInterval {a : ℕ} (z : CutRing × CutRing)
    (j : Fin 2) (u v : CutRing) :
    spatialTranslate z (coordinateInterval a j u v) =
      coordinateInterval a j (u+(if j=0 then z.1 else z.2))
        (v+(if j=0 then z.1 else z.2)) := by
  apply Subtype.ext
  ext p
  have hfract (x y : ℝ) : Int.fract (Int.fract x+y) = Int.fract (x+y) := by
    change Int.fract (x-(⌊x⌋:ℝ)+y) = _
    rw [sub_add_eq_add_sub,Int.fract_sub_intCast]
  have hsub (x y : CutRing) : v+x-(u+y) = v-u+(x-y) := by ring
  fin_cases j <;>
    simp [spatialTranslate,coordinateInterval,coordinateBetween,coordinateArc,
      coordinate,coordinateShift,translate_val,hfract,hsub,sub_eq_add_neg,add_assoc]

theorem spatialTranslate_coordinateRectangle {a : ℕ} (z : CutRing × CutRing)
    (u v : Fin 2 → CutRing) :
    spatialTranslate z (coordinateRectangle a u v) =
      coordinateRectangle a (fun j => u j+(if j=0 then z.1 else z.2))
        (fun j => v j+(if j=0 then z.1 else z.2)) := by
  simp [coordinateRectangle,spatialTranslate_coordinateInterval]

end ChartTransforms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCellPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowCellPartition

theorem windowCell_mem {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (i : Fin n) (p : GenericSquare a) :
    p ∈ (windowCell a j n q i).val ↔
      ordinary (windowCut n q i.castSucc) ≤ liftedCoordinate j ((q:CutRing)*cutTau) p ∧
      liftedCoordinate j ((q:CutRing)*cutTau) p < ordinary (windowCut n q i.succ) := by
  have hn' : (200:ℝ) < n := by exact_mod_cast (by omega : 200 < n)
  have hlen : ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) < 1 :=
    (windowCut_mesh n q i).trans_lt ((div_lt_one (by linarith)).mpr hn')
  have hord := (windowCut_strictMono n q (Fin.castSucc_lt_succ (i := i))).le
  change p ∈ coordinateBetween _ _ _ _ ↔ _
  rw [mem_coordinateBetween_iff j _ _ hord hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hb := windowCut_bounds n q i.castSucc
    have hb' := windowCut_bounds n q i.succ
    have hfloor : (⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋:ℤ) = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor <;> linarith
    simp only [liftedCoordinate,hfloor,Int.cast_neg,sub_neg_eq_add]
    exact ⟨hk,hk'⟩
  · rintro ⟨hl,hu⟩
    refine ⟨-⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋,?_,?_⟩
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hl
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hu

end WindowCellPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ClosedChartOverlap

theorem planar_lift_avoidsCuts {a : ℕ} (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : p.val = (Int.fract t.1,Int.fract t.2)) : AvoidsCuts a t := by
  have h := avoidsCuts_translate p.property.2.2
    ((⌊t.1⌋ : CutRing),(⌊t.2⌋ : CutRing))
  have he : p.val+(ordinary (⌊t.1⌋ : CutRing),ordinary (⌊t.2⌋ : CutRing)) = t := by
    rw [ht]
    apply Prod.ext
    · change Int.fract t.1+ordinary (⌊t.1⌋ : CutRing) = t.1
      rw [map_intCast]
      exact sub_add_cancel _ _
    · change Int.fract t.2+ordinary (⌊t.2⌋ : CutRing) = t.2
      rw [map_intCast]
      exact sub_add_cancel _ _
  rwa [he] at h

end ClosedChartOverlap

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_GlobalTangentChain
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section GlobalTangentChain

theorem translated_rectangle_window {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (z : CutRing × CutRing) (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives k (fun j => pointLabel z j+p j)) i).val)
      (spatialTranslate z (coordinateRectangle a l v)).val := by
  rw [spatialTranslate_coordinateRectangle]
  have hL j : pointLabel z j+p j ≤ endpointLabel (l j+pointCoordinate z j) ∧
      endpointLabel (l j+pointCoordinate z j) < pointLabel z j+p j+k := by
    simp only [endpointLabel_add,pointLabel]
    have hh := hl j
    omega
  have hV j : pointLabel z j+p j ≤ endpointLabel (v j+pointCoordinate z j) ∧
      endpointLabel (v j+pointCoordinate z j) < pointLabel z j+p j+k := by
    simp only [endpointLabel_add,pointLabel]
    have hh := hv j
    omega
  intro x y he
  exact and_congr
    (coordinateInterval_window k _ 0 _ _ (hL 0) (hV 0) x y he)
    (coordinateInterval_window k _ 1 _ _ (hL 1) (hV 1) x y he)

end GlobalTangentChain

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalChartDecisions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section LocalChartDecisions

theorem fract_fract_add_eq (x y : ℝ) :
    Int.fract (Int.fract x+y)=Int.fract (x+y) := by
  change Int.fract (x-(⌊x⌋:ℝ)+y)=_
  rw [sub_add_eq_add_sub,Int.fract_sub_intCast]

theorem translate_planar_lift {a : ℕ} (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2)) (u : CutRing × CutRing) :
    (translate a u p).val=(Int.fract (z.1+ordinary u.1),Int.fract (z.2+ordinary u.2)) := by
  simp only [translate_val,hz,fract_fract_add_eq]

end LocalChartDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowRectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowRectangles

theorem windowPlanarLift_coordinate {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a)
    (j : Fin 2) : realCoordinate (windowPlanarLift q p) j =
      liftedCoordinate j ((q j:CutRing)*cutTau) p := by fin_cases j <;> rfl

theorem windowPlanarLift_spec {a : ℕ} (q : Fin 2 → ℤ) (p : GenericSquare a) :
    p.val=(Int.fract (windowPlanarLift q p).1,Int.fract (windowPlanarLift q p).2) := by
  simp only [windowPlanarLift,liftedCoordinate,Int.fract_sub_intCast]
  apply Prod.ext
  · exact (Int.fract_eq_self.mpr p.property.1).symm
  · exact (Int.fract_eq_self.mpr p.property.2.1).symm

theorem windowRectangle_mem {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (i : Fin 2 → Fin n) (p : GenericSquare a) :
    p ∈ (windowRectangle a n q i).val ↔ ∀ j : Fin 2,
      ordinary (windowCut n (q j) (i j).castSucc) ≤ realCoordinate (windowPlanarLift q p) j ∧
      realCoordinate (windowPlanarLift q p) j < ordinary (windowCut n (q j) (i j).succ) := by
  change (p ∈ (windowCell a 0 n (q 0) (i 0)).val ∧
    p ∈ (windowCell a 1 n (q 1) (i 1)).val) ↔ _
  simp only [windowCell_mem _ n hn,windowPlanarLift_coordinate]
  rw [Fin.forall_fin_two]

theorem windowRectangle_resolved {a : ℕ} {r : CutRing} (n : ℕ) (hn : 0<n)
    (q : Fin 2 → ℤ) (i : Fin 2 → Fin n) :
    ResolvedBy (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) z).val) (windowRectangle a n q i).val := by
  intro x y he
  have hx := coordinateLabelWindow_resolved (a := a) (r := r) n q 0 _ _
      (windowCut_label n (q 0) hn (i 0).castSucc) (windowCut_label n (q 0) hn (i 0).succ) x y he
  have hy := coordinateLabelWindow_resolved (a := a) (r := r) n q 1 _ _
      (windowCut_label n (q 1) hn (i 1).castSucc) (windowCut_label n (q 1) hn (i 1).succ) x y he
  exact and_congr hx hy

end WindowRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ConcurrentGeometry

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem mesh_small : 200/(C.mesh:ℝ)<C.epsilon := by
  have h := mul_le_mul_of_nonneg_right (lineIntersectionConstant_ge_one a)
    (show 0 ≤ 200/(C.mesh:ℝ) by positivity)
  simpa only [one_mul] using h.trans_lt C.mesh_fine

theorem margin_resolved (t : VertexType (commonVertexDenominator a)) :
    ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives C.window C.start) s).val)
      (coordinateRectangle a (C.margins t).lower (C.margins t).upper).val := by
  intro x y hxy
  exact and_congr
    (coordinateLabelWindow_resolved C.window C.start 0 _ _ (C.labels t 0).1 (C.labels t 0).2 x y hxy)
    (coordinateLabelWindow_resolved C.window C.start 1 _ _ (C.labels t 1).1 (C.labels t 1).2 x y hxy)

end ConcurrentGeometry

end ConcurrentGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowClipping
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowClipping

theorem window_cell_enclosure (n : ℕ) (q : ℤ) (i : Fin n) (b e : CutRing)
    (hb : q≤endpointLabel b ∧ endpointLabel b<q+n)
    (he : q≤endpointLabel e ∧ endpointLabel e<q+n)
    (x : ℝ) (k : ℤ)
    (hx : ordinary (windowCut n q i.castSucc)≤x ∧ x<ordinary (windowCut n q i.succ))
    (hk : ordinary b≤x+(k:ℝ) ∧ x+(k:ℝ)<ordinary e) :
    ordinary b≤ordinary (windowCut n q i.castSucc)+(k:ℝ) ∧
      ordinary (windowCut n q i.succ)+(k:ℝ)≤ordinary e := by
  have hn (z : CutRing) (hz : q≤endpointLabel z ∧ endpointLabel z<q+n) :
      ¬(ordinary (windowCut n q i.castSucc)<ordinary z-(k:ℝ) ∧
        ordinary z-(k:ℝ)<ordinary (windowCut n q i.succ)) := by
    have hl : endpointLabel (z-(k:CutRing))=endpointLabel z := by simp [endpointLabel_sub]
    simpa only [map_sub,map_intCast] using
      windowCut_no_between n q i (z-(k:CutRing)) (by rwa [hl])
  constructor
  · by_contra hh
    exact hn b hb ⟨by linarith,by linarith⟩
  · by_contra hh
    exact hn e he ⟨by linarith,by linarith⟩

theorem clippedSlope_le_box {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) :
    clippedSlopePrimitive a r j ≤ coordinateRectangle a (fun _ => -r) (fun _ => r) := by
  intro p hp
  obtain ⟨k,hk,_⟩ := Set.mem_iUnion.mp hp
  have hb := (mem_circularBoxPiece r k p).mp hk
  change (p ∈ coordinateBetween a 0 (-r) r ∧ p ∈ coordinateBetween a 1 (-r) r)
  constructor
  · apply (mem_coordinateBetween_iff 0 (-r) r (by rw [map_neg]; linarith)
      (by rw [map_neg]; linarith) p).mpr
    refine ⟨-(k.1.val:ℤ),?_⟩
    simpa only [coordinate,Matrix.cons_val_zero,Matrix.cons_val_one,map_neg,Int.cast_neg,Int.cast_natCast,← sub_eq_add_neg] using hb.1
  · apply (mem_coordinateBetween_iff 1 (-r) r (by rw [map_neg]; linarith)
      (by rw [map_neg]; linarith) p).mpr
    refine ⟨-(k.2.val:ℤ),?_⟩
    simpa only [coordinate,Matrix.cons_val_zero,Matrix.cons_val_one,map_neg,Int.cast_neg,Int.cast_natCast,← sub_eq_add_neg] using hb.2

theorem windowRectangle_clipping_chart {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ j, q j≤endpointLabel (-r) ∧ endpointLabel (-r)<q j+n)
    (he : ∀ j, q j≤endpointLabel r ∧ endpointLabel r<q j+n)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val)
    (hclip : p ∈ (coordinateRectangle a (fun _ => -r) (fun _ => r)).val) :
    ∃ k : Fin 2 → ℤ, ∀ j,
      -ordinary r≤ordinary (windowCut n (q j) (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (windowCut n (q j) (cell j).succ)+(k j:ℝ)≤ordinary r := by
  have hc (j : Fin 2) : p ∈ coordinateBetween a j (-r) r := by
    fin_cases j
    · exact hclip.1
    · exact hclip.2
  have hi (j : Fin 2) := (mem_coordinateBetween_iff j (-r) r
    (by rw [map_neg]; linarith) (by rw [map_neg]; linarith) p).mp (hc j)
  choose k hk using hi
  refine ⟨fun j => k j+⌊coordinate j p-ordinary ((q j:CutRing)*cutTau)⌋,?_⟩
  intro j
  have hh := window_cell_enclosure n (q j) (cell j) (-r) r (hb j) (he j)
    (realCoordinate (windowPlanarLift q p) j)
    (k j+⌊coordinate j p-ordinary ((q j:CutRing)*cutTau)⌋)
    ((windowRectangle_mem n hn q cell p).mp hp j) ?_
  · simpa only [map_neg] using hh
  · simp only [windowPlanarLift_coordinate,liftedCoordinate,Int.cast_add]
    constructor <;> linarith [(hk j).1,(hk j).2]

theorem windowRectangle_clipped_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (k : Fin 2 → ℤ)
    (hk : ∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
      ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r)
    (p : GenericSquare a) (hp : p ∈ (windowRectangle a n q cell).val) :
    p ∈ (clippedSlopePrimitive a r j).val ↔
      0 ≤ cutForm a j ((windowPlanarLift q p).1+(k 0:ℝ),(windowPlanarLift q p).2+(k 1:ℝ)) := by
  let z := ((windowPlanarLift q p).1+(k 0:ℝ),(windowPlanarLift q p).2+(k 1:ℝ))
  have hz : p.val=(Int.fract z.1,Int.fract z.2) := by
    simpa only [z,Int.fract_add_intCast] using windowPlanarLift_spec q p
  have hbounds (d : Fin 2) : -ordinary r < realCoordinate z d ∧ realCoordinate z d<ordinary r := by
    have hm := (windowRectangle_mem n hn q cell p).mp hp d
    have hh := hk d
    have he : realCoordinate z d=realCoordinate (windowPlanarLift q p) d+(k d:ℝ) := by
      fin_cases d <;> rfl
    have hne := planar_lift_avoidsCuts p z hz (Fin.castLE (by omega) d) (-r)
    have hf : cutForm a (Fin.castLE (by omega) d) z=realCoordinate z d := by
      fin_cases d <;> rfl
    rw [hf,map_neg] at hne
    rw [he] at hne ⊢
    constructor
    · exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
    · linarith
  apply mem_clippedSlope_lift r j hr p z ⟨hbounds 0,hbounds 1⟩ hz

end WindowClipping

section ActualSlopeClassifier

theorem windowRectangle_slope_classifier {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+n)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+n) :
    (∀ p ∈ (windowRectangle a n q cell).val, p ∉ (clippedSlopePrimitive a r j).val) ∨
    ∃ k : Fin 2 → ℤ,
      (∀ d, -ordinary r≤ordinary (windowCut n (q d) (cell d).castSucc)+(k d:ℝ) ∧
        ordinary (windowCut n (q d) (cell d).succ)+(k d:ℝ)≤ordinary r) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        p ∈ (clippedSlopePrimitive a r j).val ↔
          ordinary (-integralCutForm a j ((k 0:CutRing),(k 1:CutRing))) ≤
            cutForm a j (windowPlanarLift q p) := by
  classical
  by_cases h : ∃ p ∈ (windowRectangle a n q cell).val, p ∈ (clippedSlopePrimitive a r j).val
  · obtain ⟨p,hp,hp'⟩ := h
    obtain ⟨k,hk⟩ := windowRectangle_clipping_chart r hr n hn q cell hb he p hp
      (clippedSlope_le_box r j hr hp')
    refine Or.inr ⟨k,hk,?_⟩
    intro t ht
    rw [windowRectangle_clipped_sign r j hr n hn q cell k hk t ht]
    have hadd := cutForm_add a j (windowPlanarLift q t) ((k 0:ℝ),(k 1:ℝ))
    have hord := cutForm_ordinary a j ((k 0:CutRing),(k 1:CutRing))
    simp only [map_intCast] at hord
    rw [map_neg]
    change 0 ≤ cutForm a j (windowPlanarLift q t+((k 0:ℝ),(k 1:ℝ))) ↔ _
    rw [hadd,hord]
    exact neg_le_iff_add_nonneg.symm
  · exact Or.inl (fun p hp hpp => h ⟨p,hp,hpp⟩)

end ActualSlopeClassifier

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallStarRelators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section CellConstantActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem cell_constant_action (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (b : Bool) (he : U ⊓ W = if b then W else ⊥)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)*x*
        (if b then B.c (subtypeAlternatingHom I.val (universalProjection _ s)) else 1)⁻¹ := by
  have hspec := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
  simp only [MonoidHom.comp_apply] at hspec
  cases b with
  | false =>
    have hh := B.chart_action_transfer hlarge P h U ⊥ W hU
      (fun _ _ _ => Iff.rfl) hW (by simpa using he) f hf hc I s
    simpa only [Bool.false_eq_true,↓reduceIte,B.fullGeometricSector_bot,MonoidHom.one_apply] using hh
  | true =>
    have hh := B.chart_action_transfer hlarge P h U (wholePolygon a) W hU
      (fun _ _ _ => Iff.rfl) hW (by change U ⊓ W=⊤ ⊓ W; simpa using he) f hf hc I s
    simpa only [↓reduceIte,B.fullGeometricSector_whole,MonoidHom.comp_apply,hspec] using hh

end InitialCoverSystem
end CellConstantActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalCoordinateClassifier
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section LocalCoordinateClassifier

theorem circular_interval_on_short_cell (t l u v : ℝ) (_ht : 0<t ∧ t<1)
    (_hlu : l≤u) (hmesh₁ : u-l<t) (hmesh₂ : u-l<1-t) :
    (∀ x, l≤x → x<u → Int.fract (x-v)<t) ∨
    (∀ x, l≤x → x<u → ¬ Int.fract (x-v)<t) ∨
    (∃ k : ℤ, l≤v+(k:ℝ)+t ∧ v+(k:ℝ)+t≤u ∧
      ∀ x, l≤x → x<u → (Int.fract (x-v)<t ↔ x<v+(k:ℝ)+t)) ∨
    (∃ k : ℤ, l≤v+(k:ℝ) ∧ v+(k:ℝ)≤u ∧
      ∀ x, l≤x → x<u → (Int.fract (x-v)<t ↔ v+(k:ℝ)≤x)) := by
  let k : ℤ := ⌊l-v⌋
  have hk : (k:ℝ)≤l-v ∧ l-v<(k:ℝ)+1 := ⟨Int.floor_le _,Int.lt_floor_add_one _⟩
  have hf (x : ℝ) (hl : v+(k:ℝ)≤x) (hu : x<v+(k:ℝ)+1) :
      Int.fract (x-v)=x-v-(k:ℝ) := by
    rw [Int.fract,Int.floor_eq_iff.mpr (show (k:ℝ)≤x-v ∧ x-v<(k:ℝ)+1 from
      ⟨by linarith,by linarith⟩)]
  by_cases hu : u≤v+(k:ℝ)+t
  · left
    intro x hxl hxu
    rw [hf x (by linarith [hk.1]) (by linarith [_ht.2])]
    linarith
  · by_cases hl : v+(k:ℝ)+t≤l
    · by_cases hu' : u≤v+(k:ℝ)+1
      · right; left
        intro x hxl hxu
        rw [hf x (by linarith [hk.1]) (by linarith)]
        linarith
      · right; right; right
        refine ⟨k+1,by push_cast; linarith [hk.2],by push_cast; linarith,?_⟩
        intro x hxl hxu
        by_cases hx : x<v+(k:ℝ)+1
        · rw [hf x (by linarith [hk.1]) hx]
          push_cast
          constructor <;> intro hh <;> linarith
        · have hx' : Int.fract (x-v)=x-v-((k:ℝ)+1) := by
            have he : ⌊x-v⌋=k+1 := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith [hk.2,_ht.2])
            rw [Int.fract,he]
            push_cast
            rfl
          rw [hx']
          push_cast
          constructor <;> intro hh <;> linarith [hk.2]
    · right; right; left
      refine ⟨k,by linarith,by linarith,?_⟩
      intro x hxl hxu
      rw [hf x (by linarith [hk.1]) (by linarith)]
      constructor <;> intro hh <;> linarith

end LocalCoordinateClassifier

section ActualCoordinateClassifier

theorem translated_coordinate_fract {a : ℕ} (j : Fin 2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2)) :
    p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j))<Real.goldenRatio-1 := by
  have ht := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at ht
  have hc : coordinate j (translate a (-u) p)=
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j)) := by
    fin_cases j
    · exact congrArg Prod.fst ht
    · exact congrArg Prod.snd ht
  change (cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary (cutTau-1) ∧
    ¬cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary 0) ↔ _
  have hform : cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val=
      coordinate j (translate a (-u) p) := by fin_cases j <;> rfl
  simp only [hform,map_sub,ordinary_cutTau,map_one,map_zero,not_lt,
    hc,Int.fract_nonneg,and_true]

theorem windowRectangle_coordinate_classify {a : ℕ} (n : ℕ) (hn : 201≤n)
    (hmesh₁ : 200/(n:ℝ)<Real.goldenRatio-1) (hmesh₂ : 200/(n:ℝ)<2-Real.goldenRatio)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n) (j : Fin 2) (u : CutRing × CutRing) :
    (∀ p ∈ (windowRectangle a n q cell).val,
      p ∈ (spatialTranslate u (coordinatePrimitive a j)).val) ∨
    (∀ p ∈ (windowRectangle a n q cell).val,
      p ∉ (spatialTranslate u (coordinatePrimitive a j)).val) ∨
    (∃ b : CutRing, ordinary (windowCut n (q j) (cell j).castSucc)≤ordinary b ∧
      ordinary b≤ordinary (windowCut n (q j) (cell j).succ) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        (p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
          realCoordinate (windowPlanarLift q p) j<ordinary b)) ∨
    (∃ b : CutRing, ordinary (windowCut n (q j) (cell j).castSucc)≤ordinary b ∧
      ordinary b≤ordinary (windowCut n (q j) (cell j).succ) ∧
      ∀ p ∈ (windowRectangle a n q cell).val,
        (p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
          ordinary b ≤ realCoordinate (windowPlanarLift q p) j)) := by
  have hh := circular_interval_on_short_cell (Real.goldenRatio-1)
    (ordinary (windowCut n (q j) (cell j).castSucc))
    (ordinary (windowCut n (q j) (cell j).succ)) (ordinary (pointCoordinate u j))
    ⟨by linarith [Real.one_lt_goldenRatio],by linarith [Real.goldenRatio_lt_two]⟩
    (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := cell j))).le
    ((windowCut_mesh n (q j) (cell j)).trans_lt hmesh₁)
    (by have h := (windowCut_mesh n (q j) (cell j)).trans_lt hmesh₂; linarith)
  rcases hh with h | h | ⟨k,hk,hk',h⟩ | ⟨k,hk,hk',h⟩
  · left
    intro p hp
    rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
    have hb := (windowRectangle_mem n hn q cell p).mp hp j
    exact h _ hb.1 hb.2
  · right; left
    intro p hp
    rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
    have hb := (windowRectangle_mem n hn q cell p).mp hp j
    exact h _ hb.1 hb.2
  · right; right; left
    refine ⟨pointCoordinate u j+(k:CutRing)+(cutTau-1),?_,?_,?_⟩
    · simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using hk
    · simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using hk'
    · intro p hp
      rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
      have hb := (windowRectangle_mem n hn q cell p).mp hp j
      simpa only [map_add,map_sub,map_intCast,ordinary_cutTau,map_one] using h _ hb.1 hb.2
  · right; right; right
    refine ⟨pointCoordinate u j+(k:CutRing),?_,?_,?_⟩
    · simpa only [map_add,map_intCast] using hk
    · simpa only [map_add,map_intCast] using hk'
    · intro p hp
      rw [translated_coordinate_fract j u p _ (windowPlanarLift_spec q p)]
      have hb := (windowRectangle_mem n hn q cell p).mp hp j
      simpa only [map_add,map_intCast] using h _ hb.1 hb.2

end ActualCoordinateClassifier

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VaryingCellClassification
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section VaryingCellClassification

theorem varying_cell_classification {a : ℕ} (r : CutRing)
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (C : ConcurrentGeometry a r) (q : Fin 2 → ℤ)
    (hb : ∀ d, q d≤endpointLabel (-r) ∧ endpointLabel (-r)<q d+C.mesh)
    (he : ∀ d, q d≤endpointLabel r ∧ endpointLabel r<q d+C.mesh)
    (cell : Fin 2 → Fin C.mesh) (d j : Fin 2) (v : CutRing × CutRing) :
    (∃ b : Bool, clippedSlopePrimitive a r (slopeDirection d) ⊓ windowRectangle a C.mesh q cell=
      if b then windowRectangle a C.mesh q cell else ⊥) ∨
    (∃ b : Bool, spatialTranslate v (coordinatePrimitive a j) ⊓ windowRectangle a C.mesh q cell=
      if b then windowRectangle a C.mesh q cell else ⊥) ∨
    ∃ k : Fin 2 → ℤ, ∃ c : CutRing, ∃ positive : Bool,
      (∀ l, -ordinary r≤ordinary (windowCut C.mesh (q l) (cell l).castSucc)+(k l:ℝ) ∧
        ordinary (windowCut C.mesh (q l) (cell l).succ)+(k l:ℝ)≤ordinary r) ∧
      (∀ p ∈ (windowRectangle a C.mesh q cell).val,
        (p ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
          if positive then ordinary c ≤ realCoordinate (windowPlanarLift q p) j
          else realCoordinate (windowPlanarLift q p) j<ordinary c)) ∧
      ∃ x y v' w : GenericSquare a,
        x ∈ (windowRectangle a C.mesh q cell).val ∧
        y ∈ (windowRectangle a C.mesh q cell).val ∧
        v' ∈ (windowRectangle a C.mesh q cell).val ∧
        w ∈ (windowRectangle a C.mesh q cell).val ∧
        cutForm a (slopeDirection d) (windowPlanarLift q x)≤
          ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing))) ∧
        ordinary (-integralCutForm a (slopeDirection d) ((k 0:CutRing),(k 1:CutRing)))≤
          cutForm a (slopeDirection d) (windowPlanarLift q y) ∧
        cutForm a (axisDirection j) (windowPlanarLift q v')≤ordinary c ∧
        ordinary c ≤ cutForm a (axisDirection j) (windowPlanarLift q w) := by
  classical
  let W := windowRectangle a C.mesh q cell
  let U := clippedSlopePrimitive a r (slopeDirection d)
  let V := spatialTranslate v (coordinatePrimitive a j)
  have hconst (E : polygonAlgebra a) (b : Bool)
      (hh : ∀ p ∈ W.val, p ∈ E.val ↔ b=true) : E ⊓ W=if b then W else ⊥ := by
    apply Subtype.ext
    ext p
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at hh ⊢
    · change (p ∈ E.val ∧ p ∈ W.val) ↔ False
      exact ⟨fun hp => (hh p hp.2).mp hp.1,False.elim⟩
    · change (p ∈ E.val ∧ p ∈ W.val) ↔ p ∈ W.val
      exact ⟨And.right,fun hp => ⟨(hh p hp).mpr trivial,hp⟩⟩
  by_cases hp : ∀ p ∈ W.val, p ∈ U.val
  · exact Or.inl ⟨true,hconst U true (fun p h => iff_of_true (hp p h) rfl)⟩
  by_cases hp' : ∀ p ∈ W.val, p ∉ U.val
  · exact Or.inl ⟨false,hconst U false (fun p h => iff_of_false (hp' p h) Bool.noConfusion)⟩
  by_cases hv : ∀ p ∈ W.val, p ∈ V.val
  · exact Or.inr (Or.inl ⟨true,hconst V true (fun p h => iff_of_true (hv p h) rfl)⟩)
  by_cases hv' : ∀ p ∈ W.val, p ∉ V.val
  · exact Or.inr (Or.inl ⟨false,hconst V false (fun p h => iff_of_false (hv' p h) Bool.noConfusion)⟩)
  push Not at hp hp' hv hv'
  obtain ⟨x,hx,hxn⟩ := hp
  obtain ⟨y,hy,hyp⟩ := hp'
  obtain ⟨v',hvv,hvn⟩ := hv
  obtain ⟨w,hw,hwp⟩ := hv'
  obtain hs | ⟨k,hk,hks⟩ := windowRectangle_slope_classifier r (slopeDirection d) hr C.mesh C.mesh_large q cell hb he
  · exact (hs y hy hyp).elim
  have hcx := le_of_lt (lt_of_not_ge (fun heq => hxn ((hks x hx).mpr heq)))
  have hcy := (hks y hy).mp hyp
  have hgap₁ : 200/(C.mesh:ℝ)<Real.goldenRatio-1 := by
    have he := C.mesh_small; have hp := C.positive; have hg := C.first_gap; linarith
  have hgap₂ : 200/(C.mesh:ℝ)<2-Real.goldenRatio := by
    have he := C.mesh_small; have hp := C.positive; have hg := C.second_gap; linarith
  obtain hc | hc | ⟨c,_hc₁,_hc₂,hc⟩ | ⟨c,_hc₁,_hc₂,hc⟩ :=
    windowRectangle_coordinate_classify C.mesh C.mesh_large hgap₁ hgap₂ q cell j v
  · exact (hvn (hc v' hvv)).elim
  · exact (hc w hw hwp).elim
  · refine Or.inr (Or.inr ⟨k,c,false,hk,by simpa only [Bool.false_eq_true,↓reduceIte] using hc,
      x,y,w,v',hx,hy,hw,hvv,hcx,hcy,?_,?_⟩)
    · simpa only [cutForm_axis] using ((hc w hw).mp hwp).le
    · simpa only [cutForm_axis] using (not_lt.mp (fun hh => hvn ((hc v' hvv).mpr hh)))
  · refine Or.inr (Or.inr ⟨k,c,true,hk,by simpa only [↓reduceIte] using hc,
      x,y,v',w,hx,hy,hvv,hw,hcx,hcy,?_,?_⟩)
    · simpa only [cutForm_axis] using (le_of_lt (lt_of_not_ge (fun hh => hvn ((hc v' hvv).mpr hh))))
    · simpa only [cutForm_axis] using (hc w hw).mp hwp

end VaryingCellClassification

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConstantCellTemplates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ConstantCellTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {J : Type*} {κ : Type} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem constant_cell_template (hlarge : 20 ≤ m+1)
    (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
    (U : Fin 2 → polygonAlgebra a) (W : polygonAlgebra a)
    (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i) (U i))
    (hU : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i) j).val) (U i).val)
    (hW : ∀ i, ResolvedBy (fun j => (primitiveTests (a := a) (r := r) (P i) j).val) W.val)
    (hf : ∀ j, B.AlignedSmallSupported (f j))
    (hc : ∀ i j, SmallControlled B.c (f j) (B.fullGeometricSector (by omega) (P i) (h i) W))
    (i i' : Fin 2) (hne : i≠i') (positive : Bool)
    (he : U i ⊓ W=if positive then W else ⊥) :
    Nonempty (B.LocalPatchTemplate (by omega) F f) := by
  classical
  let V : polygonAlgebra a := if positive then wholePolygon a else ⊥
  let R : Fin 2 → polygonAlgebra a := fun j => if j=i then V else U i'
  refine ⟨{ index := κ
            tests := P i'
            lawful := h i'
            margin := W
            predicates := R
            margin_resolved := hW i'
            predicates_resolved := ?_
            controlled := hc i'
            action := ?_ }⟩
  · intro j
    by_cases hj : j=i
    · simp only [R,hj,↓reduceIte]
      cases positive <;> exact fun _ _ _ => Iff.rfl
    · simpa only [R,hj,↓reduceIte] using hU i'
  · intro j I s l x hx
    let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
    by_cases hj : j=i
    · subst j
      rw [hF]
      have hh := B.cell_constant_action hlarge (P i) (h i) (U i) W (hU i) (hW i)
        positive he (f l) (hf l) (hc i l) I' s x hx
      have hπ := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
      simp only [MonoidHom.comp_apply] at hπ
      cases positive <;>
        simpa only [R,V,Bool.false_eq_true,↓reduceIte,B.fullGeometricSector_whole,B.fullGeometricSector_bot,
          MonoidHom.comp_apply,MonoidHom.one_apply,hπ] using hh
    · have hj' : j=i' := by
        fin_cases i <;> fin_cases i' <;> fin_cases j <;> simp_all
      subst j
      simp only [R,Ne.symm hne,↓reduceIte,hF]

end InitialCoverSystem
end ConstantCellTemplates

section SlopeCoordinateCellTemplate
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

theorem slope_coordinate_cell_template_oai {κ : Type} [Finite κ] {J : Type*}
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (v : CutRing × CutRing)
    (P : Fin 2 → κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P i))
    (i₀ i₁ : κ) (hP : P 0 i₀=(slopeTestIndex d,0)) (hQ : P 1 i₁=(coordinateTestIndex j,v))
    (F : Option (Fin 2) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hF : ∀ i, F (some i)=B.fullGeometricSector (by omega) (P i) (h i)
      (![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)] i))
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin A.geometry.mesh)
    (hb : ∀ k, q k ≤ endpointLabel (-r) ∧ endpointLabel (-r)<q k+A.geometry.mesh)
    (he : ∀ k, q k ≤ endpointLabel r ∧ endpointLabel r<q k+A.geometry.mesh)
    (hW : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val)
      (windowRectangle a A.geometry.mesh q cell).val)
    (hcoherent : ∀ i, B.fullGeometricSector (by omega) (P i) (h i)
      (windowRectangle a A.geometry.mesh q cell)=B.windowSector (by omega) A.geometry.mesh
        (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))
    (hf : ∀ l, B.AlignedSmallSupported (f l))
    (hcontrol : ∀ l, SmallControlled B.c (f l) (B.windowSector (by omega) A.geometry.mesh
      (A.rectangles.rectangles A.geometry.mesh) q (windowRectangle a A.geometry.mesh q cell))) :
    Nonempty (B.LocalPatchTemplate (by omega) F f) := by
  let U : Fin 2 → polygonAlgebra a :=
    ![clippedSlopePrimitive a r (slopeDirection d),spatialTranslate v (coordinatePrimitive a j)]
  have hU : ∀ i, ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r) (P i) s).val) (U i).val := by
    intro i x y hxy
    fin_cases i
    · change x ∈ (clippedSlopePrimitive a r (slopeDirection d)).val ↔
        y ∈ (clippedSlopePrimitive a r (slopeDirection d)).val
      have hh := hxy i₀
      change x ∈ (spatialTranslate (P 0 i₀).2 (initialTest a r (P 0 i₀).1)).val ↔
        y ∈ (spatialTranslate (P 0 i₀).2 (initialTest a r (P 0 i₀).1)).val at hh
      simpa only [hP,initialTest_slope,spatialTranslate_zero] using hh
    · change x ∈ (spatialTranslate v (coordinatePrimitive a j)).val ↔
        y ∈ (spatialTranslate v (coordinatePrimitive a j)).val
      have hh := hxy i₁
      change x ∈ (spatialTranslate (P 1 i₁).2 (initialTest a r (P 1 i₁).1)).val ↔
        y ∈ (spatialTranslate (P 1 i₁).2 (initialTest a r (P 1 i₁).1)).val at hh
      simpa only [hQ,initialTest_coordinate] using hh
  have hctrl : ∀ i l, SmallControlled B.c (f l) (B.fullGeometricSector (by omega) (P i) (h i)
      (windowRectangle a A.geometry.mesh q cell)) := by
    intro i l
    rw [hcoherent i]
    exact hcontrol l
  obtain ⟨b,hb'⟩ | ⟨b,hb'⟩ | ⟨k,c,positive,hk,hc,x,y,v',w,hx,hy,hv,hw,hcx,hcy,hdv,hdw⟩ :=
    varying_cell_classification r hr A.geometry q hb he cell d j v
  · exact B.constant_cell_template hlarge F f P h U _ hF hU hW hf hctrl 0 1 (by decide) b hb'
  · exact B.constant_cell_template hlarge F f P h U _ hF hU hW hf hctrl 1 0 (by decide) b hb'
  · obtain ⟨t,u,hinc,hact⟩ := A.crossing_cell_actions hlarge hr ha (P 0) (P 1) (h 0) (h 1)
      i₀ i₁ d j v hP hQ q cell k c positive hk hc x y v' w hx hy hv hw hcx hcy hdv hdw
    let R : Fin 2 → polygonAlgebra a := ![
      spatialTranslate (u+A.geometry.anchors t (slopeDirection d)) (clippedSlopePrimitive a r (slopeDirection d)),
      if positive then spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j)
        else (spatialTranslate (u+A.geometry.anchors t (axisDirection j)) (coordinatePrimitive a j))ᶜ]
    have hrMargin : ResolvedBy (fun s => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (A.concurrentPrimitives t u) s).val) (A.margin t u).val := by
      intro x y hh
      exact translatedTemplate_resolved (Sum.elim
        (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
        (coordinateWindowPrimitives A.geometry.window A.geometry.start))
        (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
        (fun x y hh => A.geometry.margin_resolved t x y (fun i => hh (Sum.inr i))) u x y hh
    have hrc : ∀ l, SmallControlled B.c (f l)
        (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) (A.margin t u)) := by
      intro l
      apply B.all_rectangle_control_to_template hlarge A.rectangles.rectangles A.geometry.window
        A.geometry.start u (A.concurrentPrimitives t u) (A.concurrentLaw t u) Sum.inr (fun _ => rfl)
        _ (A.geometry.margin_resolved t)
        (translated_rectangle_window A.geometry.start u _ _
          (fun j => (A.geometry.labels t j).1) (fun j => (A.geometry.labels t j).2))
        A.geometry.mesh q _
        (windowRectangle_resolved A.geometry.mesh (by have hh := A.geometry.mesh_large; omega) q cell)
        hinc (f l) (hf l) (hcontrol l)
    refine ⟨{ index := Sum (Fin 4) (Fin 2 × Fin (A.geometry.window-1))
              tests := A.concurrentPrimitives t u
              lawful := A.concurrentLaw t u
              margin := A.margin t u
              predicates := R
              margin_resolved := hrMargin
              predicates_resolved := ?_
              controlled := hrc
              action := ?_ }⟩
    · intro l x y hh
      fin_cases l
      · change x ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (clippedSlopePrimitive a r (slopeDirection d))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (clippedSlopePrimitive a r (slopeDirection d))).val
        have hs := hh (Sum.inl (slopeDirection d))
        change x ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (initialTest a r (slopeTestIndex d))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (slopeDirection d))
            (initialTest a r (slopeTestIndex d))).val at hs
        simpa only [initialTest_slope] using hs
      · have hs := hh (Sum.inl (axisDirection j))
        change x ∈ (spatialTranslate (u+A.geometry.anchors t (axisDirection j))
            (initialTest a r (coordinateTestIndex j))).val ↔
          y ∈ (spatialTranslate (u+A.geometry.anchors t (axisDirection j))
            (initialTest a r (coordinateTestIndex j))).val at hs
        rw [initialTest_coordinate] at hs
        cases positive <;> change _ ↔ _
        · exact not_congr hs
        · exact hs
    · intro l I s l' x hx'
      let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
      have hh := hact (f l') (hf l') (hcontrol l') I' s x hx'
      rw [hF]
      fin_cases l
      · exact hh.1
      · exact hh.2

end InitialCoverSystem.PatchAtlas
end SlopeCoordinateCellTemplate

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.slope_coordinate_cell_template_oai.{u_1}
