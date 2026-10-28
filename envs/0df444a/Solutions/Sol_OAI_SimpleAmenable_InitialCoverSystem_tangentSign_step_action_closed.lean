-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:03:19.322928+00:00
-- url     : https://prove2.me/submissions/f92843a8-af7f-4b74-8834-b052fde5f881

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ResolvedBoolean
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
section ChartQuadrants

theorem coordinateRectangle_lift {a : ℕ} (u v : Fin 2 → CutRing)
    (huv : ∀ j, ordinary (u j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (u j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a u v).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) ∧
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) := by
  change p ∈ coordinateBetween a 0 (u 0) (v 0) ∧
    p ∈ coordinateBetween a 1 (u 1) (v 1) at hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff 0 (u 0) (v 0) (huv 0) (hlen 0) p).mp hp.1
  obtain ⟨l,hl⟩ := (mem_coordinateBetween_iff 1 (u 1) (v 1) (huv 1) (hlen 1) p).mp hp.2
  refine ⟨(coordinate 0 p+(k:ℝ),coordinate 1 p+(l:ℝ)),?_,hk,hl⟩
  simp only [Int.fract_add_intCast,Int.fract_eq_self.mpr (coordinate_bounds 0 p),
    Int.fract_eq_self.mpr (coordinate_bounds 1 p)]
  rfl

end ChartQuadrants

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SpatialChartGeometry

theorem translated_clippedSlope_lift {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u : CutRing × CutRing)
    (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : p.val = (Int.fract t.1,Int.fract t.2))
    (hp : (-ordinary r < t.1-ordinary u.1 ∧ t.1-ordinary u.1 < ordinary r) ∧
      (-ordinary r < t.2-ordinary u.2 ∧ t.2-ordinary u.2 < ordinary r)) :
    p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j t := by
  change translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔ _
  rw [mem_clippedSlope_lift r j hr (translate a (-u) p)
    (t-(ordinary u.1,ordinary u.2)) hp ?_]
  · rw [cutForm_sub,cutForm_ordinary]
    exact sub_nonneg
  · have hfract (x y : ℝ) : Int.fract (Int.fract x+y) = Int.fract (x+y) := by
      change Int.fract (x-(⌊x⌋:ℝ)+y) = _
      rw [sub_add_eq_add_sub,Int.fract_sub_intCast]
    simp [ht,hfract,sub_eq_add_neg]

end SpatialChartGeometry

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentChartTemplates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section TangentChartTemplates

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_first (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (e : Fin 5) (positive : Bool) :
    B.tangentSign hlarge k p u h d z positive =
      B.fullGeometricSector hlarge
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
        (if positive then spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))
          else (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d)))ᶜ) := by
  unfold tangentSign
  refine B.fullGeometricSector_shared_primitive hlarge
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0)) z)
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2)) ?_ (h d 0 z) (h d e z) _ ?_
  · simp only [translatedTemplate,tangentChartTemplate,ite_true]
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate (z+0) (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope] at hh
    cases positive with
    | false => simpa using (not_congr hh)
    | true => simpa using hh

theorem tangentSign_second (hlarge : 15 < m+1) (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing)
    (h : B.TangentChartLaws k p u) (d : Fin 2) (z : CutRing × CutRing) (e : Fin 5) (positive : Bool) :
    B.tangentSign hlarge k p u h d (z+tangentOffset a d (signedShortSteps u e)) positive =
      B.fullGeometricSector hlarge
        (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
        (if positive then spatialTranslate (z+tangentOffset a d (signedShortSteps u e))
            (clippedSlopePrimitive a r (slopeDirection d))
          else (spatialTranslate (z+tangentOffset a d (signedShortSteps u e))
            (clippedSlopePrimitive a r (slopeDirection d)))ᶜ) := by
  unfold tangentSign
  refine B.fullGeometricSector_shared_primitive hlarge
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u 0))
      (z+tangentOffset a d (signedShortSteps u e)))
    (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
    (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) ?_ (h d 0 _) (h d e z) _ ?_
  · simp [translatedTemplate,tangentChartTemplate]
  · intro x y he
    have hh := he ()
    change x ∈ (spatialTranslate ((z+tangentOffset a d (signedShortSteps u e))+0)
        (initialTest a r (slopeTestIndex d))).val ↔
      y ∈ (spatialTranslate ((z+tangentOffset a d (signedShortSteps u e))+0)
        (initialTest a r (slopeTestIndex d))).val at hh
    simp only [add_zero,initialTest_slope] at hh
    cases positive with
    | false => simpa using (not_congr hh)
    | true => simpa using hh

end InitialCoverSystem
end TangentChartTemplates

section TangentChartAction

theorem tangentChart_first_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate z (clippedSlopePrimitive a r (slopeDirection d))).val := by
  intro x y he
  have hh := he (Sum.inl 0)
  simpa [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    tangentChartTemplate] using hh

theorem tangentChart_second_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate (z+tangentOffset a d e) (clippedSlopePrimitive a r (slopeDirection d))).val := by
  intro x y he
  have hh := he (Sum.inl 1)
  simpa [InitialCoverSystem.primitiveTests,primitiveFamilyTests,translatedTemplate,
    tangentChartTemplate] using hh

theorem tangentChart_rectangle_resolved {a k : ℕ} {r : CutRing}
    (p : Fin 2 → ℤ) (d : Fin 2) (e : CutRing) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (translatedTemplate (tangentChartTemplate a k p d e) z) i).val)
      (spatialTranslate z (coordinateRectangle a l v)).val := by
  apply translatedTemplate_resolved
  intro x y he
  exact and_congr
    (coordinateLabelWindow_resolved k p 0 (l 0) (v 0) (hl 0) (hv 0) x y
      (fun i => he (Sum.inr i)))
    (coordinateLabelWindow_resolved k p 1 (l 1) (v 1) (hl 1) (hv 1) x y
      (fun i => he (Sum.inr i)))

end TangentChartAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem coordinateRectangle_strict_lift {a : ℕ} (l h : Fin 2 → CutRing)
    (hlh : ∀ j, ordinary (l j) ≤ ordinary (h j))
    (hlen : ∀ j, ordinary (h j)-ordinary (l j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a l h).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (l 0) < t.1 ∧ t.1 < ordinary (h 0)) ∧
      (ordinary (l 1) < t.2 ∧ t.2 < ordinary (h 1)) := by
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift l h hlh hlen p hp
  have hx' := planar_lift_avoidsCuts p t ht 0 (l 0)
  have hy' := planar_lift_avoidsCuts p t ht 1 (l 1)
  simp only [cutForm,Matrix.cons_val_zero,Matrix.cons_val_one] at hx' hy'
  exact ⟨t,ht,⟨lt_of_le_of_ne hx.1 (Ne.symm hx'),hx.2⟩,
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hy'),hy.2⟩⟩

theorem clippedSlope_agree_on_closed_rectangle {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (u v : CutRing × CutRing) (l h : Fin 2 → CutRing)
    (hlh : ∀ k, ordinary (l k) ≤ ordinary (h k))
    (hlen : ∀ k, ordinary (h k)-ordinary (l k) < 1)
    (hu : ∀ k, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate u k) ∧
      ordinary (h k)-ordinary (pointCoordinate u k) ≤ ordinary r)
    (hv : ∀ k, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate v k) ∧
      ordinary (h k)-ordinary (pointCoordinate v k) ≤ ordinary r)
    (hline : integralCutForm a j u = integralCutForm a j v) :
    spatialTranslate u (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h =
      spatialTranslate v (clippedSlopePrimitive a r j) ⊓ coordinateRectangle a l h := by
  apply Subtype.ext
  ext p
  change (p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val) ↔
    (p ∈ (spatialTranslate v (clippedSlopePrimitive a r j)).val ∧
    p ∈ (coordinateRectangle a l h).val)
  by_cases hp : p ∈ (coordinateRectangle a l h).val
  · obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_strict_lift l h hlh hlen p hp
    have hbox (w : CutRing × CutRing)
        (hw : ∀ k : Fin 2, -ordinary r ≤ ordinary (l k)-ordinary (pointCoordinate w k) ∧
          ordinary (h k)-ordinary (pointCoordinate w k) ≤ ordinary r) :
        (-ordinary r < t.1-ordinary w.1 ∧ t.1-ordinary w.1 < ordinary r) ∧
          (-ordinary r < t.2-ordinary w.2 ∧ t.2-ordinary w.2 < ordinary r) := by
      have hw0 := hw 0
      have hw1 := hw 1
      simp only [pointCoordinate,ite_true,Fin.isValue,show (1:Fin 2) ≠ 0 by decide,ite_false] at hw0 hw1
      constructor <;> constructor <;> linarith
    rw [translated_clippedSlope_lift r j hr u p t ht (hbox u hu),
      translated_clippedSlope_lift r j hr v p t ht (hbox v hv),hline]
  · simp only [hp,and_false]

end ClosedChartOverlap

section FullTangentOverlap

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_step_action_closed_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r ≤ ordinary (l j) ∧ ordinary (v j) ≤ ordinary r)
    (hbox' : ∀ j, -ordinary r ≤ ordinary (l j)-ordinary
          (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
        ordinary (v j)-ordinary
          (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ≤ ordinary r)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega)
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.tangentSign (by omega) k p u h d (z+tangentOffset a d (signedShortSteps u e)) true
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  rw [B.tangentSign_first (by omega) k p u h d z e true,
    B.tangentSign_second (by omega) k p u h d z e true]
  apply B.chart_action_transfer hlarge _ (h d e z) _ _ _
    (tangentChart_first_resolved p d _ z) (tangentChart_second_resolved p d _ z)
    (tangentChart_rectangle_resolved p d _ z l v hl hv) _ f hf hc I s
  have he := clippedSlope_agree_on_closed_rectangle (a := a) r (slopeDirection d) hr
    (0 : CutRing × CutRing) (tangentOffset a d (signedShortSteps u e)) l v hlv hlen
    (by simpa [pointCoordinate] using hbox) hbox'
    (by simp only [integralCutForm_zero,integralCutForm_tangentOffset])
  have he' := congrArg (spatialTranslate z) he
  simpa only [spatialTranslate_inter,← spatialTranslate_add,add_zero] using he'

end InitialCoverSystem
end FullTangentOverlap

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed_oai := @OAI.SimpleAmenable.InitialCoverSystem.tangentSign_step_action_closed_oai
