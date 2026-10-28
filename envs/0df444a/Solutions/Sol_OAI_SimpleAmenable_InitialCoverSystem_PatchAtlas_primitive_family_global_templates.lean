-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:58:33.081155+00:00
-- url     : https://prove2.me/submissions/940e3db0-f500-460d-a79f-766c2a81b33c

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_family_local_templates

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCells
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowCells

attribute [local instance] cutOrdinaryOrder

theorem windowInterior_zero (n : ℕ) (hn : 0 < n) :
    windowInterior n ⟨0,hn⟩ = 0 := by
  have hmem : (0:CutRing) ∈ windowEndpointSet n := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0,hn⟩,Finset.mem_univ _,by simp⟩
  have hrange := Finset.range_orderEmbOfFin (windowEndpointSet n) (windowEndpointSet_card n)
  have hx : (0:CutRing) ∈ Set.range (windowInterior n) := by
    change (0:CutRing) ∈ Set.range ((windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n))
    rw [hrange]; exact hmem
  obtain ⟨i,hi⟩ := hx
  apply ordinary_injective
  have hle := (windowInterior n).monotone (show (⟨0,hn⟩:Fin n) ≤ i by exact Nat.zero_le _)
  change ordinary (windowInterior n ⟨0,hn⟩) ≤ ordinary (windowInterior n i) at hle
  rw [hi,map_zero] at hle
  rw [map_zero]
  exact le_antisymm hle (windowInterior_bounds n ⟨0,hn⟩).1

theorem windowCut_zero (n : ℕ) (q : ℤ) (hn : 0 < n) :
    windowCut n q 0 = (q:CutRing)*cutTau := by
  simp only [windowCut,Fin.val_zero,dite_eq_left hn,windowInterior_zero n hn,add_zero]

theorem windowCut_last (n : ℕ) (q : ℤ) :
    windowCut n q (Fin.last n) = (q:CutRing)*cutTau+1 := by
  simp [windowCut]

end WindowCells

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

theorem finite_interval_cell {n : ℕ} {x : Fin (n+1) → ℝ}
    (_hn : 1 ≤ n) (t : ℝ) (hl : x 0 ≤ t) (hu : t < x (Fin.last n)) :
    ∃ i : Fin n, x i.castSucc ≤ t ∧ t < x i.succ := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ.filter fun i => x i ≤ t
  have hS : S.Nonempty := ⟨0,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hl⟩
  let i := S.max' hS
  have hi : x i ≤ t := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hin : i.val < n := by
    have hil : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    by_contra hh
    have he : i = Fin.last n := Fin.ext (by change i.val = n; omega)
    rw [he] at hi
    linarith
  refine ⟨⟨i.val,hin⟩,hi,?_⟩
  by_contra hh
  have hj : (⟨i.val+1,by omega⟩ : Fin (n+1)) ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact le_of_not_gt hh
  have he := Finset.le_max' S _ hj
  change i.val+1 ≤ i.val at he
  omega

theorem liftedCoordinate_bounds {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) :
    ordinary z ≤ liftedCoordinate j z p ∧ liftedCoordinate j z p < ordinary z+1 := by
  have hh := Int.fract_nonneg (coordinate j p-ordinary z)
  have hh' := Int.fract_lt_one (coordinate j p-ordinary z)
  simp only [Int.fract,liftedCoordinate] at *
  constructor <;> linarith

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

theorem windowCell_cover {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (p : GenericSquare a) : ∃ i : Fin n, p ∈ (windowCell a j n q i).val := by
  have hb := liftedCoordinate_bounds j ((q:CutRing)*cutTau) p
  have hz := windowCut_zero n q (by omega)
  have hh := windowCut_last n q
  obtain ⟨i,hi⟩ := finite_interval_cell (x := fun i => ordinary (windowCut n q i))
    (by omega) (liftedCoordinate j ((q:CutRing)*cutTau) p)
    (by simpa only [hz] using hb.1) (by simpa only [hh,map_add,map_one] using hb.2)
  exact ⟨i,(windowCell_mem j n hn q i p).mpr hi⟩

end WindowCellPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowRectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem windowRectangle_cover {a : ℕ} (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ)
    (p : GenericSquare a) : ∃ i : Fin 2 → Fin n, p ∈ (windowRectangle a n q i).val := by
  have hh (j : Fin 2) := windowCell_cover (a := a) j n hn (q j) p
  choose i hi using hh
  refine ⟨i,hi 0,hi 1⟩

end WindowRectangles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section ClosedCellTemplates

theorem closedWindow_diameter (n : ℕ) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (x y : ℝ × ℝ)
    (hx : ∀ d, ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate x d ∧
      realCoordinate x d ≤ ordinary (windowCut n (q d) (cell d).succ))
    (hy : ∀ d, ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate y d ∧
      realCoordinate y d ≤ ordinary (windowCut n (q d) (cell d).succ)) :
    dist x y ≤ 200/(n:ℝ) := by
  have h (d : Fin 2) : |realCoordinate x d-realCoordinate y d| ≤ 200/(n:ℝ) := by
    have hh := windowCut_mesh n (q d) (cell d)
    have hx' := hx d
    have hy' := hy d
    apply abs_le.mpr
    constructor <;> linarith
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  exact ⟨h 0,h 1⟩

end ClosedCellTemplates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CompactFineGrid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CompactFineGrid

theorem closedWindowBox_subset (n : ℕ) (cell : Fin 2 → Fin n) :
    closedWindowBox n cell ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  intro p hp
  have h (j : Fin 2) : realCoordinate p j ∈ Set.Icc (0:ℝ) 1 := by
    have hl := (windowCut_bounds n 0 (cell j).castSucc).1
    have hu := (windowCut_bounds n 0 (cell j).succ).2
    simp only [Int.cast_zero,zero_mul,map_zero,zero_add] at hl hu
    exact ⟨hl.trans (hp j).1,(hp j).2.trans hu⟩
  exact ⟨h 0,h 1⟩

theorem closedWindowBox_nonempty (n : ℕ) (cell : Fin 2 → Fin n) :
    (closedWindowBox n cell).Nonempty := by
  refine ⟨(ordinary (windowCut n 0 (cell 0).castSucc),
    ordinary (windowCut n 0 (cell 1).castSucc)),?_⟩
  intro j
  have he : realCoordinate
      (ordinary (windowCut n 0 (cell 0).castSucc),
       ordinary (windowCut n 0 (cell 1).castSucc)) j =
      ordinary (windowCut n 0 (cell j).castSucc) := by fin_cases j <;> rfl
  rw [he]
  exact ⟨le_rfl,(windowCut_strictMono n 0 (Fin.castSucc_lt_succ (i := cell j))).le⟩

theorem compact_open_cover_fine_grid {ι : Type*}
    (O : ι → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 201 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      200/(n:ℝ) < ε ∧ ∀ cell : Fin 2 → Fin n, ∃ i,
        closedWindowBox n cell ⊆ O i := by
  obtain ⟨δ,hδ,hlocal⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc) hO hcover
  have hmin : 0 < min δ ε := lt_min hδ hε
  obtain ⟨N,hN⟩ := exists_nat_gt (200/min δ ε)
  refine ⟨max 201 N,le_max_left _ _,fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmesh : 200/(n:ℝ) < min δ ε := by
    rw [div_lt_iff₀ hnpos]
    have hNN : (N:ℝ) ≤ n := by exact_mod_cast hnN
    have hlt := (div_lt_iff₀ hmin).mp hN
    nlinarith
  refine ⟨hmesh.trans_le (min_le_right _ _),fun cell => ?_⟩
  obtain ⟨x,hx⟩ := closedWindowBox_nonempty n cell
  obtain ⟨i,hi⟩ := hlocal x (closedWindowBox_subset n cell hx)
  refine ⟨i,fun p hp => hi ?_⟩
  apply Metric.mem_ball.mpr
  exact (closedWindow_diameter n (fun _ => 0) cell p x hp hx).trans_lt
    (hmesh.trans_le (min_le_left _ _))

theorem compact_local_bounds_fine_grid {ι : Type*}
    (O : ι → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ N : ℕ, 201 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ cell : Fin 2 → Fin n, ∃ i,
        200/(n:ℝ) < ε i ∧ closedWindowBox n cell ⊆ O i := by
  classical
  obtain ⟨s,hs⟩ := (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover O hO hcover
  have hspos : s.Nonempty := by
    have hh := hs (show ((0,0) : ℝ × ℝ) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 from
      ⟨⟨le_rfl,by norm_num⟩,⟨le_rfl,by norm_num⟩⟩)
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hi,_⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi⟩
  obtain ⟨i₀,_,hi₀⟩ := s.exists_min_image ε hspos
  have hcov : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i : s, O i.val := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hx⟩
  obtain ⟨N,hN,hfine⟩ := compact_open_cover_fine_grid (fun i : s => O i.val)
    (fun i => hO i.val) hcov (ε i₀) (hε i₀)
  refine ⟨N,hN,fun n hn cell => ?_⟩
  obtain ⟨hmesh,hcells⟩ := hfine n hn
  obtain ⟨i,hi⟩ := hcells cell
  exact ⟨i.val,hmesh.trans_le (hi₀ i.val i.property),hi⟩

end CompactFineGrid

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteRefiningGrid
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
section FiniteRefiningGrid
attribute [local instance] cutOrdinaryOrder

theorem finite_refining_grid (S : Finset CutRing) (n : ℕ) (_hn : 0<n) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i : Fin (n+1), windowCut n 0 i ∈ Set.range e) := by
  classical
  let T : Finset CutRing := insert 1 (insert 0 ((S.image cutFraction) ∪ windowEndpointSet n))
  have h0 : (0:CutRing) ∈ T := by simp [T]
  have h1 : (1:CutRing) ∈ T := by simp [T]
  have hcard : 2 ≤ T.card := by
    have hh : ({0,1} : Finset CutRing) ⊆ T := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨h0,h1⟩
    have hh' := Finset.card_le_card hh
    simpa only [Finset.card_insert_of_notMem (by simp : (0:CutRing) ∉ ({1} : Finset CutRing)),Finset.card_singleton] using hh'
  let N := T.card-1
  have hN : 0<N := by dsimp [N]; omega
  have hc : T.card=N+1 := by dsimp [N]; omega
  let e : Fin (N+1) ↪o CutRing := T.orderEmbOfFin hc
  have he (c : CutRing) : c ∈ Set.range e ↔ c ∈ T := by
    rw [Finset.range_orderEmbOfFin]; rfl
  have hb (i : Fin (N+1)) : 0≤ordinary (e i) ∧ ordinary (e i)≤1 := by
    have hi := Finset.orderEmbOfFin_mem T hc i
    change e i ∈ T at hi
    simp only [T,Finset.mem_insert,Finset.mem_union,Finset.mem_image] at hi
    rcases hi with hi | hi | ⟨c,hc,heq⟩ | hi
    · simp only [hi,map_one,zero_le_one,le_refl,and_self]
    · simp only [hi,map_zero,le_refl,zero_le_one,and_self]
    · rw [← heq,ordinary_cutFraction]; exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    · rw [windowEndpointSet,Finset.mem_image] at hi
      obtain ⟨c,_,heq⟩ := hi
      rw [← heq,ordinary_cutFraction]; exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have hzero : e 0=0 := by
    obtain ⟨i,hi⟩ := (he 0).mpr h0
    apply ordinary_injective
    have hh : ordinary (e 0)≤ordinary (e i) := e.monotone (Fin.zero_le i)
    rw [hi,map_zero ordinary] at hh
    simpa only [map_zero ordinary] using le_antisymm hh (hb 0).1
  have hlast : e (Fin.last N)=1 := by
    obtain ⟨i,hi⟩ := (he 1).mpr h1
    apply ordinary_injective
    have hh : ordinary (e i)≤ordinary (e (Fin.last N)) := e.monotone (Fin.le_last i)
    rw [hi,map_one] at hh
    simpa only [map_one ordinary] using le_antisymm (hb (Fin.last N)).2 hh
  refine ⟨N,hN,e,e.strictMono,hzero,hlast,?_,?_⟩
  · intro c hc
    apply (he _).mpr
    simp only [T,Finset.mem_insert,Finset.mem_union]
    exact Or.inr (Or.inr (Or.inl (Finset.mem_image.mpr ⟨c,hc,rfl⟩)))
  · intro i
    apply (he _).mpr
    by_cases hi : i.val<n
    · have hh : windowCut n 0 i=windowInterior n ⟨i.val,hi⟩ := by simp [windowCut,hi]
      rw [hh]
      simp only [T,Finset.mem_insert,Finset.mem_union]
      exact Or.inr (Or.inr (Or.inr (windowInterior_mem n _)))
    · have hi' : i=Fin.last n := by apply Fin.ext; change i.val=n; omega
      rw [hi',windowCut_last]
      simpa using h1

theorem finite_grid_no_between {N : ℕ} {e : Fin (N+1) → CutRing}
    (he : StrictMono (fun i => ordinary (e i))) (i : Fin N) {c : CutRing}
    (hc : c ∈ Set.range e) :
    ¬(ordinary (e i.castSucc)<ordinary c ∧ ordinary c<ordinary (e i.succ)) := by
  obtain ⟨j,rfl⟩ := hc
  rintro ⟨hl,hu⟩
  have h₁ := he.lt_iff_lt.mp hl
  have h₂ := he.lt_iff_lt.mp hu
  change i.val < j.val at h₁
  change j.val < i.val+1 at h₂
  omega

theorem finite_grid_refines_window {N n : ℕ} (hn : 0<n)
    (e : Fin (N+1) → CutRing) (he : StrictMono (fun i => ordinary (e i)))
    (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hcuts : ∀ j : Fin (n+1), windowCut n 0 j ∈ Set.range e) (i : Fin N) :
    ∃ j : Fin n,
      ordinary (windowCut n 0 j.castSucc)≤ordinary (e i.castSucc) ∧
      ordinary (e i.succ)≤ordinary (windowCut n 0 j.succ) := by
  have h0 : 0≤ordinary (e i.castSucc) := by
    have hh := he.monotone (Fin.zero_le i.castSucc); simpa only [hzero,map_zero] using hh
  have h1 : ordinary (e i.castSucc)<1 := by
    have hh := he (show i.castSucc<Fin.last N from by exact i.isLt)
    simpa only [hlast,map_one] using hh
  have hz : ordinary (windowCut n 0 0)=0 := by simp [windowCut_zero n 0 hn]
  have ht : ordinary (windowCut n 0 (Fin.last n))=1 := by simp [windowCut_last]
  obtain ⟨j,hj⟩ := finite_interval_cell hn (ordinary (e i.castSucc))
    (x := fun j => ordinary (windowCut n 0 j)) (by rwa [hz]) (by rwa [ht])
  refine ⟨j,hj.1,?_⟩
  exact le_of_not_gt (fun h => finite_grid_no_between he i (hcuts j.succ) ⟨hj.2,h⟩)

end FiniteRefiningGrid

section RefinementPartition

theorem coordinateInterval_mem_preferred {a : ℕ} (j : Fin 2) (u v : CutRing)
    (hlo : 0≤ordinary u) (huv : ordinary u≤ordinary v) (hup : ordinary v≤1)
    (hlen : ordinary v-ordinary u<1) (p : GenericSquare a) :
    p ∈ (coordinateInterval a j u v).val ↔
      ordinary u ≤ coordinate j p ∧ coordinate j p<ordinary v := by
  change p ∈ coordinateBetween a j u v ↔ _
  rw [mem_coordinateBetween_iff j u v huv hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hp := coordinate_bounds j p
    have hk₁ : (-1:ℝ)<k := by linarith [hp.2]
    have hk₂ : (k:ℝ)<1 := by linarith [hp.1]
    have hk₁' : (-1:ℤ)<k := by exact_mod_cast hk₁
    have hk₂' : k<(1:ℤ) := by exact_mod_cast hk₂
    have hk0 : k=0 := by omega
    simpa only [hk0,Int.cast_zero,add_zero] using And.intro hk hk'
  · exact fun h => ⟨0,by simpa using h.1,by simpa using h.2⟩

theorem refinedGridRectangle_mem {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (p : GenericSquare a) :
    p ∈ (refinedGridRectangle a N e cell).val ↔ ∀ j : Fin 2,
      ordinary (e (cell j).castSucc) ≤ coordinate j p ∧ coordinate j p<ordinary (e (cell j).succ) := by
  have h (j : Fin 2) := coordinateInterval_mem_preferred j (e (cell j).castSucc) (e (cell j).succ)
    (by have hh := he.monotone (Fin.zero_le (cell j).castSucc); simpa only [hzero,map_zero] using hh)
    (he (Fin.castSucc_lt_succ (i := cell j))).le
    (by have hh := he.monotone (Fin.le_last (cell j).succ); simpa only [hlast,map_one] using hh)
    (hmesh (cell j)) p
  change (p ∈ (coordinateInterval a 0 _ _).val ∧ p ∈ (coordinateInterval a 1 _ _).val) ↔ _
  rw [h 0,h 1,Fin.forall_fin_two]

theorem refinedGridRectangle_resolved {a N : ℕ} (r : CutRing) (e : Fin (N+1) → CutRing) :
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ, ∀ cell : Fin 2 → Fin N,
      ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val := by
  obtain ⟨n,q,hq⟩ := finite_coordinate_windows_container (fun _ : Fin (N+1) => 1)
    (fun i _ => endpointLabel (e i))
  have hl (i : Fin (N+1)) (j : Fin 2) : q j≤endpointLabel (e i) ∧ endpointLabel (e i)<q j+n := by
    have hh := hq i j
    constructor <;> omega
  refine ⟨n,q,fun cell x y hh => ?_⟩
  exact and_congr
    (coordinateInterval_window n q 0 _ _ (hl _ 0) (hl _ 0) x y hh)
    (coordinateInterval_window n q 1 _ _ (hl _ 1) (hl _ 1) x y hh)

end RefinementPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RefinedEndpointDecisions
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
section RefinedEndpointDecisions

theorem finite_grid_endpoint_sides {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (c : CutRing) (hc : cutFraction c ∈ Set.range e) (k : ℤ) :
    ordinary c-(k:ℝ)≤ordinary (e i.castSucc) ∨ ordinary (e i.succ)≤ordinary c-(k:ℝ) := by
  by_contra hh
  push Not at hh
  have hlo : 0≤ordinary (e i.castSucc) := by
    have h := he.monotone (Fin.zero_le i.castSucc)
    simpa only [hzero,map_zero] using h
  have hup : ordinary (e i.succ)≤1 := by
    have h := he.monotone (Fin.le_last i.succ)
    simpa only [hlast,map_one] using h
  have hf : ⌊ordinary c⌋=k := Int.floor_eq_iff.mpr ⟨by linarith,by linarith⟩
  have hfrac : ordinary (cutFraction c)=ordinary c-(k:ℝ) := by rw [ordinary_cutFraction,Int.fract,hf]
  exact finite_grid_no_between he i hc (by rw [hfrac]; exact ⟨hh.1,hh.2⟩)

end RefinedEndpointDecisions

section ClosedRefinementContainment

theorem finite_grid_interval_lift {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (u v : CutRing)
    (hu : cutFraction u ∈ Set.range e) (hv : cutFraction v ∈ Set.range e)
    (x : ℝ) (hx : ordinary (e i.castSucc)≤x ∧ x<ordinary (e i.succ))
    (k : ℤ) (hk : ordinary u≤x+(k:ℝ) ∧ x+(k:ℝ)<ordinary v) :
    ordinary u≤ordinary (e i.castSucc)+(k:ℝ) ∧ ordinary (e i.succ)+(k:ℝ)≤ordinary v := by
  constructor
  · rcases finite_grid_endpoint_sides e he hzero hlast i u hu k with hh | hh
    · linarith
    · linarith [hx.2,hk.1]
  · rcases finite_grid_endpoint_sides e he hzero hlast i v hv k with hh | hh
    · linarith [hx.1,hk.2]
    · linarith

theorem refinedGridRectangle_nonempty {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) : (refinedGridRectangle a N e cell).val.Nonempty := by
  let O : Set (ℝ × ℝ) := (Set.Ioo (ordinary (e (cell 0).castSucc)) (ordinary (e (cell 0).succ))) ×ˢ
    (Set.Ioo (ordinary (e (cell 1).castSucc)) (ordinary (e (cell 1).succ)))
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_Ioo
  have hne : O.Nonempty := Set.Nonempty.prod
    (Set.nonempty_Ioo.mpr (he (Fin.castSucc_lt_succ (i := cell 0))))
    (Set.nonempty_Ioo.mpr (he (Fin.castSucc_lt_succ (i := cell 1))))
  obtain ⟨p,hp,hg⟩ := (avoidsCuts_dense a).inter_open_nonempty O hO hne
  have hbounds (j : Fin 2) : 0≤ordinary (e (cell j).castSucc) ∧ ordinary (e (cell j).succ)≤1 := by
    constructor
    · have hh := he.monotone (Fin.zero_le (cell j).castSucc); simpa only [hzero,map_zero] using hh
    · have hh := he.monotone (Fin.le_last (cell j).succ); simpa only [hlast,map_one] using hh
  have hsq : p.1 ∈ Set.Ico (0:ℝ) 1 ∧ p.2 ∈ Set.Ico (0:ℝ) 1 :=
    ⟨⟨(hbounds 0).1.trans hp.1.1.le,hp.1.2.trans_le (hbounds 0).2⟩,
     ⟨(hbounds 1).1.trans hp.2.1.le,hp.2.2.trans_le (hbounds 1).2⟩⟩
  let x : GenericSquare a := ⟨p,hsq.1,hsq.2,hg⟩
  refine ⟨x,(refinedGridRectangle_mem e he hzero hlast hmesh cell x).mpr ?_⟩
  intro j
  fin_cases j
  · exact ⟨hp.1.1.le,hp.1.2⟩
  · exact ⟨hp.2.1.le,hp.2.2⟩

theorem refinedGridRectangle_closed_lift {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (u v : Fin 2 → CutRing)
    (hu : ∀ j, cutFraction (u j) ∈ Set.range e) (hv : ∀ j, cutFraction (v j) ∈ Set.range e)
    (huv : ∀ j, ordinary (u j)≤ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (u j)<1)
    (x : GenericSquare a) (hx : x ∈ (refinedGridRectangle a N e cell).val)
    (hR : x ∈ (coordinateRectangle a u v).val) :
    ∃ k : Fin 2 → ℤ, ∀ j,
      ordinary (u j)≤ordinary (e (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (e (cell j).succ)+(k j:ℝ)≤ordinary (v j) := by
  have hp (j : Fin 2) : x ∈ coordinateBetween a j (u j) (v j) := by
    fin_cases j
    · exact hR.1
    · exact hR.2
  have hh (j : Fin 2) := (mem_coordinateBetween_iff j (u j) (v j) (huv j) (hlen j) x).mp (hp j)
  choose k hk using hh
  exact ⟨k,fun j => finite_grid_interval_lift e he hzero hlast (cell j) (u j) (v j)
    (hu j) (hv j) (coordinate j x)
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx j) (k j) (hk j)⟩

end ClosedRefinementContainment

section CommonTranslatedGrid

theorem refinedGridRectangle_translated_window {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (v : CutRing × CutRing)
    (hcuts : ∀ j : Fin 2, ∀ i : Fin (n+1),
      cutFraction (windowCut n (q j) i+pointCoordinate v j) ∈ Set.range e) :
    ∃ old : Fin 2 → Fin n, ∃ k : Fin 2 → ℤ, ∀ j,
      ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
        ordinary (e (cell j).castSucc)+(k j:ℝ) ∧
      ordinary (e (cell j).succ)+(k j:ℝ)≤
        ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty (a := a) e he hzero hlast hmesh cell
  obtain ⟨old,ho⟩ := windowRectangle_cover n hn q (translate a (-v) x)
  have hR : x ∈ (spatialTranslate v (windowRectangle a n q old)).val := ho
  rw [windowRectangle,spatialTranslate_coordinateRectangle] at hR
  have hpos : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
  have hlen (j) : ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j)-
      ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)<1 := by
    simp only [map_add,add_sub_add_right_eq_sub]
    exact (windowCut_mesh n (q j) (old j)).trans_lt ((div_lt_one (by linarith)).mpr hpos)
  have hle (j) : ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
      ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
    simp only [map_add,add_le_add_iff_right]
    exact (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := old j))).le
  exact ⟨old,refinedGridRectangle_closed_lift e he hzero hlast hmesh cell _ _
    (fun j => hcuts j _) (fun j => hcuts j _) hle hlen x hx (by simpa only [pointCoordinate] using hR)⟩

theorem common_translated_grid {ι : Type*} [Fintype ι]
    (S : Finset CutRing) (n : ℕ) (hn : 201≤n)
    (size : ι → ℕ) (_hs : ∀ i, 201 ≤ size i) (q : ι → Fin 2 → ℤ) (v : ι → CutRing × CutRing) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)≤200/(n:ℝ)) ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i, ∀ j : Fin 2, ∀ k : Fin (size i+1),
        cutFraction (windowCut (size i) (q i j) k+pointCoordinate (v i) j) ∈ Set.range e) ∧
      (∀ i : Fin N, ∃ k : Fin n,
        ordinary (windowCut n 0 k.castSucc)≤ordinary (e i.castSucc) ∧
        ordinary (e i.succ)≤ordinary (windowCut n 0 k.succ)) := by
  classical
  let U : Finset CutRing := S ∪ Finset.univ.biUnion (fun i : ι =>
    Finset.univ.biUnion (fun j : Fin 2 => (Finset.univ : Finset (Fin (size i+1))).image
      (fun k => windowCut (size i) (q i j) k+pointCoordinate (v i) j)))
  obtain ⟨N,hN,e,he,hzero,hlast,hcuts,hfine⟩ := finite_refining_grid U n (by omega)
  have href := finite_grid_refines_window (by omega : 0<n) e he hzero hlast hfine
  refine ⟨N,hN,e,he,hzero,hlast,?_,?_,?_,href⟩
  · intro i
    obtain ⟨k,hk₁,hk₂⟩ := href i
    have hm := windowCut_mesh n 0 k
    linarith
  · intro c hc
    exact hcuts c (Finset.mem_union_left _ hc)
  · intro i j k
    apply hcuts
    simp only [U,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and]
    exact Or.inr ⟨i,j,k,rfl⟩

end CommonTranslatedGrid

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CompactCommonRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CompactCommonRefinement

theorem compact_common_refining_grid {ι κ : Type*} [Fintype ι]
    (S : Finset CutRing) (size : ι → ℕ) (hs : ∀ i, 201 ≤ size i)
    (q : ι → Fin 2 → ℤ) (v : ι → CutRing × CutRing)
    (O : κ → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ i, O i)
    (ε : κ → ℝ) (hε : ∀ i, 0<ε i) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
      StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
      (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
      (∀ c ∈ S, cutFraction c ∈ Set.range e) ∧
      (∀ i, ∀ j : Fin 2, ∀ k : Fin (size i+1),
        cutFraction (windowCut (size i) (q i j) k+pointCoordinate (v i) j) ∈ Set.range e) ∧
      (∀ cell : Fin 2 → Fin N, ∃ k, closedRefinedBox N e cell ⊆ O k ∧
        ∀ j, ordinary (e (cell j).succ)-ordinary (e (cell j).castSucc)<ε k) := by
  obtain ⟨n,hn,hfine⟩ := compact_local_bounds_fine_grid O hO hcover ε hε
  obtain ⟨N,hN,e,he,hzero,hlast,hmesh,hS,hcuts,href⟩ := common_translated_grid S n hn size hs q v
  have hnpos : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
  refine ⟨N,hN,e,he,hzero,hlast,fun i => (hmesh i).trans_lt
    ((div_lt_one (by linarith)).mpr hnpos),hS,hcuts,?_⟩
  intro cell
  have hh (j : Fin 2) := href (cell j)
  choose old hold using hh
  obtain ⟨k,hδ,hk⟩ := hfine n le_rfl old
  refine ⟨k,fun p hp => hk (fun j => ⟨(hold j).1.trans (hp j).1,(hp j).2.trans (hold j).2⟩),?_⟩
  intro j
  exact (hmesh (cell j)).trans_lt hδ

end CompactCommonRefinement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RefinementNeighborhoods
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
section RefinementNeighborhoods

theorem refinedGridRectangle_subset_translated_window {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (v : CutRing × CutRing)
    (hcuts : ∀ j : Fin 2, ∀ i : Fin (n+1),
      cutFraction (windowCut n (q j) i+pointCoordinate v j) ∈ Set.range e) :
    ∃ old : Fin 2 → Fin n,
      refinedGridRectangle a N e cell ≤ spatialTranslate v (windowRectangle a n q old) := by
  obtain ⟨old,k,hk⟩ := refinedGridRectangle_translated_window (a := a) e he hzero hlast hmesh cell n hn q v hcuts
  refine ⟨old,?_⟩
  intro p hp
  have hpm := (refinedGridRectangle_mem e he hzero hlast hmesh cell p).mp hp
  rw [windowRectangle,spatialTranslate_coordinateRectangle]
  have h (j : Fin 2) : p ∈ coordinateBetween a j
      (windowCut n (q j) (old j).castSucc+pointCoordinate v j)
      (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
    have hle : ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)≤
        ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j) := by
      simp only [map_add,add_le_add_iff_right]
      exact (windowCut_strictMono n (q j) (Fin.castSucc_lt_succ (i := old j))).le
    have hlen : ordinary (windowCut n (q j) (old j).succ+pointCoordinate v j)-
        ordinary (windowCut n (q j) (old j).castSucc+pointCoordinate v j)<1 := by
      simp only [map_add,add_sub_add_right_eq_sub]
      have hn' : (200:ℝ)<n := by exact_mod_cast (by omega : 200<n)
      exact (windowCut_mesh n (q j) (old j)).trans_lt ((div_lt_one (by linarith)).mpr hn')
    apply (mem_coordinateBetween_iff j _ _ hle hlen p).mpr
    refine ⟨k j,?_,?_⟩
    · linarith [(hpm j).1,(hk j).1]
    · linarith [(hpm j).2,(hk j).2]
  exact ⟨h 0,h 1⟩

theorem closedRefinedBox_endpoint_near {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (cell : Fin 2 → Fin N)
    (z : ℝ × ℝ) (δ : ℝ) (h : closedRefinedBox N e cell ⊆ Metric.ball z δ) :
    ∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ := by
  have hl : (ordinary (e (cell 0).castSucc),ordinary (e (cell 1).castSucc)) ∈ closedRefinedBox N e cell := by
    intro k
    fin_cases k <;> exact ⟨le_rfl,(he (Fin.castSucc_lt_succ (i := cell _))).le⟩
  have hu : (ordinary (e (cell 0).succ),ordinary (e (cell 1).succ)) ∈ closedRefinedBox N e cell := by
    intro k
    fin_cases k <;> exact ⟨(he (Fin.castSucc_lt_succ (i := cell _))).le,le_rfl⟩
  have hL := h hl
  have hU := h hu
  rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff] at hL hU
  intro k
  fin_cases k
  · exact ⟨hL.1,hU.1⟩
  · exact ⟨hL.2,hU.2⟩

end RefinementNeighborhoods

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGlobalTemplates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitive_family_global_templates_oai {ι : Type*} [Finite ι]
    (ha : 0<a) (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin (N+1) → CutRing,
    StrictMono (fun i => ordinary (e i)) ∧ e 0=0 ∧ e (Fin.last N)=1 ∧
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) ∧
    ∃ n : ℕ, ∃ q : Fin 2 → ℤ,
    (∀ cell : Fin 2 → Fin N,
      ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
        (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val) ∧
    ∀ (cell : Fin 2 → Fin N) (J : Type)
      (f : J → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)),
    (∀ v, B.AlignedSmallSupported (f v)) →
    (∀ v, SmallControlled B.c (f v) (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell))) →
    ∃ L : B.LocalPatchTemplate (by omega) (A.starFamily (by omega) P) f,
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
  classical
  let _ := Fintype.ofFinite ι
  let Z := {z : ℝ × ℝ // z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1}
  have hlocal (z : Z) := A.primitive_family_local_templates ha hlarge hr P z.val z.property.1 z.property.2 hmesh
  choose G δ hδ htemplates using hlocal
  let O : Z → Set (ℝ × ℝ) := fun z => Metric.ball z.val (δ z)
  have hO z : IsOpen (O z) := Metric.isOpen_ball
  have hcover : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ z, O z := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,Metric.mem_ball_self (hδ ⟨z,hz⟩)⟩
  obtain ⟨s,hs⟩ := (isCompact_Icc.prod isCompact_Icc).elim_finite_subcover O hO hcover
  have hcov : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 ⊆ ⋃ z : s, O z.val := by
    intro x hx
    obtain ⟨z,hz⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hz,hx⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hx⟩
  let S : Finset CutRing := Finset.univ.biUnion (fun z : s => Finset.univ.biUnion (fun i : ι =>
    Finset.univ.biUnion (fun k : Fin 2 =>
      {pointCoordinate (G z.val i).oldOffset k-r,pointCoordinate (G z.val i).oldOffset k+r})))
  have hSlo (z : s) (i : ι) (k : Fin 2) : pointCoordinate (G z.val i).oldOffset k-r ∈ S := by
    simp only [S,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨z,i,k,Or.inl rfl⟩
  have hShi (z : s) (i : ι) (k : Fin 2) : pointCoordinate (G z.val i).oldOffset k+r ∈ S := by
    simp only [S,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨z,i,k,Or.inr rfl⟩
  obtain ⟨N,hN,e,he,hzero,hlast,hfine,hends,hgrids,hboxes⟩ := compact_common_refining_grid S
    (fun _ : s × ι => A.geometry.mesh) (fun _ => A.geometry.mesh_large)
    (fun _ => symmetricWindowStart r) (fun k => (G k.1.val k.2).oldOffset)
    (fun z : s => O z.val) (fun z => hO z.val) hcov (fun _ => 1) (fun _ => by norm_num)
  obtain ⟨n,q,hW⟩ := refinedGridRectangle_resolved (a := a) r e
  refine ⟨N,hN,e,he,hzero,hlast,hfine,n,q,hW,?_⟩
  intro cell J f hf hc
  obtain ⟨z,hz,_⟩ := hboxes cell
  have hnear := closedRefinedBox_endpoint_near e he cell z.val.val (δ z.val) hz
  exact htemplates z.val N e he hzero hlast hfine
    (fun i k => hends _ (hSlo z i k)) (fun i k => hends _ (hShi z i k))
    cell hnear n q (hW cell)
    (fun i => refinedGridRectangle_subset_translated_window e he hzero hlast hfine cell
      A.geometry.mesh A.geometry.mesh_large (symmetricWindowStart r) (G z.val i).oldOffset
      (hgrids (z,i))) J f hf hc

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.primitive_family_global_templates_oai.{u_1}
