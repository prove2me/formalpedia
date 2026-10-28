-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:54:49.093992+00:00
-- url     : https://prove2.me/submissions/0c540917-f148-420b-9b23-b60093456333

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_CoordinateGerm_model_formula
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_coordinate_control_inward_gate
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
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

theorem translated_clippedSlope_planar {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hnear : |z.1-ordinary u.1|<ordinary r ∧ |z.2-ordinary u.2|<ordinary r) :
    p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j z := by
  change translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔ _
  have hp := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at hp
  rw [mem_clippedSlope_lift r j hr _ (z-(ordinary u.1,ordinary u.2))
    ⟨abs_lt.mp hnear.1,abs_lt.mp hnear.2⟩ hp,cutForm_sub,cutForm_ordinary]
  exact sub_nonneg

theorem fract_coordinate_sign (x : ℝ)
    (hl : -(2-Real.goldenRatio)<x) (hu : x<Real.goldenRatio-1) :
    Int.fract x<Real.goldenRatio-1 ↔ 0≤x := by
  have hτ := Real.one_lt_goldenRatio
  have hτ' := Real.goldenRatio_lt_two
  by_cases hx : 0≤x
  · rw [Int.fract_eq_self.mpr ⟨hx,by linarith⟩]
    exact iff_of_true hu hx
  · have hxf : Int.fract x=x+1 := by
      rw [← Int.fract_add_one x,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]
    rw [hxf]
    exact iff_of_false (by linarith) hx

theorem translated_coordinate_planar {a : ℕ} (j : Fin 2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hl : -(2-Real.goldenRatio) < realCoordinate z j-ordinary (pointCoordinate u j))
    (hu : realCoordinate z j-ordinary (pointCoordinate u j)<Real.goldenRatio-1) :
    p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate u j) ≤ realCoordinate z j := by
  have ht := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at ht
  have hc : coordinate j (translate a (-u) p)=
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j)) := by
    fin_cases j
    · exact congrArg Prod.fst ht
    · exact congrArg Prod.snd ht
  have hmem : p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      coordinate j (translate a (-u) p)<Real.goldenRatio-1 := by
    change (cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary (cutTau-1) ∧
      ¬cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary 0) ↔ _
    have hform : cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val=
        coordinate j (translate a (-u) p) := by fin_cases j <;> rfl
    simp only [hform,map_sub,ordinary_cutTau,map_one,map_zero,not_lt,
      (coordinate_bounds j (translate a (-u) p)).1,and_true]
  rw [hmem,hc,fract_coordinate_sign _ hl hu]
  exact sub_nonneg

end LocalChartDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VertexMargins
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
section VertexMargins

namespace VertexMargin
variable {z : ℝ × ℝ} {ε : ℝ} (V : VertexMargin z ε)

theorem width (_hε : 0<ε) (j : Fin 2) :
    ordinary (V.lower j)<ordinary (V.upper j) ∧
    ordinary (V.upper j)-ordinary (V.lower j)<4*ε := by
  have h₁ := V.lower_inner j
  have h₂ := V.upper_inner j
  have h₃ := V.lower_outer j
  have h₄ := V.upper_outer j
  constructor <;> linarith

end VertexMargin

end VertexMargins

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SupportedCellPatching
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

section ConcurrentAxisDecisions

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem axis_on_margin (j : Fin 2) (u b : CutRing × CutRing)
    (t : VertexType (commonVertexDenominator a))
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate b k)|<3*C.epsilon)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
      realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (spatialTranslate b (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate b j) ≤ realCoordinate z j := by
  have hh := abs_lt.mp (hnear z hcell j)
  apply translated_coordinate_planar j b p z hz
  · have hg := C.second_gap
    have hp := C.positive
    linarith
  · have hg := C.first_gap
    have hp := C.positive
    linarith

end ConcurrentGeometry
end ConcurrentAxisDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GridFormalPatching
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

section CoordinateGlobalActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem coordinate_charts_action (hlarge : 20 ≤ m+1)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (j' : κ → Fin 2) (u' : κ → CutRing × CutRing)
    (V V' W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (fun i => (coordinateTestIndex (j i),u i)) i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (fun i => (coordinateTestIndex (j' i),u' i)) i).val) V'.val)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) W.val)
    (heq : V ⊓ W=V' ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j i),u i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j i),u i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j' i),u' i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V'
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (fun i => (coordinateTestIndex (j' i),u' i))
        (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V'
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let J : Sum (Sum ι κ) (Fin 2 × Fin (n-1)) → Fin 2 := Sum.elim (Sum.elim j j') Prod.fst
  let Z : Sum (Sum ι κ) (Fin 2 × Fin (n-1)) → CutRing × CutRing :=
    Sum.elim (Sum.elim u u') (fun i => (coordinateWindowPrimitives n q i).2)
  let P := fun i => (coordinateTestIndex (J i),Z i)
  have h := fun I (_ : I.card≤15) b hb => B.coordinateFamilyLaw_all g J Z I b hb
  have h₀ := B.fullGeometricSector_subfamily (by omega) P _ (Sum.inl ∘ Sum.inl) rfl h
    (fun I _ b hb => B.coordinateFamilyLaw_all g j u I b hb) V hV
  have h₁ := B.fullGeometricSector_subfamily (by omega) P _ (Sum.inl ∘ Sum.inr) rfl h
    (fun I _ b hb => B.coordinateFamilyLaw_all g j' u' I b hb) V' hV'
  have h₂ := B.fullGeometricSector_subfamily (by omega) P (coordinateWindowPrimitives n q) Sum.inr rfl h
    (fun I _ b hb => g n I b hb q) W hW
  change SmallControlled B.c f (B.fullGeometricSector (by omega) (coordinateWindowPrimitives n q)
    (fun I _ b hb => g n I b hb q) W) at hc
  rw [h₂] at hc
  simp only [Function.comp_def,P,J,Z,Sum.elim_inl,Sum.elim_inr] at h₀ h₁
  rw [h₀,h₁]
  exact B.chart_action_transfer hlarge P h V V' W
    (fun x y he => hV x y (fun i => he (Sum.inl (Sum.inl i))))
    (fun x y he => hV' x y (fun i => he (Sum.inl (Sum.inr i))))
    (fun x y he => hW x y (fun i => he (Sum.inr i))) heq f hf hc I s

end InitialCoverSystem
end CoordinateGlobalActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InwardPlanarGerms
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

section ConcurrentPositiveDecisions
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem positiveDecision_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (j : Fin 4)
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate (u+C.anchors t j) k)|<3*C.epsilon)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.positiveDecision t u j).val ↔
      ordinary (integralCutForm a j (u+C.anchors t j)) ≤ cutForm a j y := by
  have hs : |y.1-ordinary (u+C.anchors t j).1|<ordinary r ∧
      |y.2-ordinary (u+C.anchors t j).2|<ordinary r := by
    have h₀ := hnear y hcell 0
    have h₁ := hnear y hcell 1
    have hr' := C.radius
    have hε := C.positive
    change |y.1-ordinary (u+C.anchors t j).1|<3*C.epsilon at h₀
    change |y.2-ordinary (u+C.anchors t j).2|<3*C.epsilon at h₁
    constructor <;> linarith
  fin_cases j
  · exact C.axis_on_margin 0 u (u+C.anchors t 0) t hnear p y hy hcell
  · exact C.axis_on_margin 1 u (u+C.anchors t 1) t hnear p y hy hcell
  · exact translated_clippedSlope_planar r 2 hr (u+C.anchors t 2) p y hy hs
  · exact translated_clippedSlope_planar r 3 hr (u+C.anchors t 3) p y hy hs

end ConcurrentGeometry
end ConcurrentPositiveDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LocalArrangementAssignments
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

section LocalBooleanAssignments
variable {a : ℕ} {ι κ : Type*}

theorem polygonFormalMask_mem (U : κ → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) (p : GenericSquare a) :
    polygonAssignment U p ∈ polygonFormalMask U V ↔ p ∈ V.val := by
  constructor
  · rintro ⟨q,hq,hqV⟩
    exact (hV q p ((polygonAssignment_eq_iff U q p).mp hq)).mp hqV
  · intro hp; exact ⟨p,rfl,hp⟩

theorem localCutFamily_locally_eq [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ p : GenericSquare a, p.val ∈ N →
        polygonAssignment (localCutFamily j c z) p=
          polygonAssignment (fun k => cutPolygon a (j k) (c k)) p := by
  classical
  let N : Set (ℝ × ℝ) := ⋂ k,
    if cutForm a (j k) z=ordinary (c k) then Set.univ
    else if cutForm a (j k) z<ordinary (c k)
    then {p | cutForm a (j k) p<ordinary (c k)}
    else {p | ordinary (c k) < cutForm a (j k) p}
  refine ⟨N,?_,?_,?_⟩
  · apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt (cutForm_continuous a (j k)) continuous_const
    · exact isOpen_lt continuous_const (cutForm_continuous a (j k))
  · apply Set.mem_iInter.mpr
    intro k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · rw [ite_eq_left he]; trivial
    · rw [ite_eq_right he]
      by_cases hl : cutForm a (j k) z<ordinary (c k)
      · rw [ite_eq_left hl]; exact hl
      · rw [ite_eq_right hl]; exact lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
  · intro p hp
    funext k
    have hk := Set.mem_iInter.mp hp k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · simp [polygonAssignment,localCutFamily,he]
    · by_cases hl : cutForm a (j k) z<ordinary (c k)
      · simp only [ite_eq_right he,ite_eq_left hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,hk]
      · simp only [ite_eq_right he,ite_eq_right hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,not_lt_of_gt hk]

theorem localPolygonFamily_locally_eq [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ)
    (R : ι → polygonAlgebra a)
    (hR : ∀ i, ResolvedBy (fun k => halfPlane a (j k) (c k)) (R i).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ p : GenericSquare a, p.val ∈ N → ∀ i,
        p ∈ (localPolygonFamily j c z R i).val ↔ p ∈ (R i).val := by
  obtain ⟨N,hN,hz,h⟩ := localCutFamily_locally_eq (a := a) j c z
  refine ⟨N,hN,hz,fun p hp i => ?_⟩
  change polygonAssignment (localCutFamily j c z) p ∈ polygonFormalMask _ (R i) ↔ _
  rw [h p hp]
  exact polygonFormalMask_mem _ (R i) (hR i) p

end LocalBooleanAssignments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InwardMargins
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
section InwardMargins
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem mem_marginPolygon_of_planar (hr : ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.marginPolygon t u).val := by
  have hw (k) := (C.margins t).width C.positive k
  have hlen (k) : ordinary ((C.margins t).upper k+pointCoordinate u k)-
      ordinary ((C.margins t).lower k+pointCoordinate u k)<1 := by
    simp only [map_add]
    linarith [hw k,C.radius]
  have hle (k) : ordinary ((C.margins t).lower k+pointCoordinate u k) ≤
      ordinary ((C.margins t).upper k+pointCoordinate u k) := by
    simp only [map_add]
    linarith [hw k]
  have hh (k) : p ∈ coordinateBetween a k
      ((C.margins t).lower k+pointCoordinate u k)
      ((C.margins t).upper k+pointCoordinate u k) := by
    rw [mem_coordinateBetween_iff k _ _ (hle k) (hlen k)]
    refine ⟨⌊realCoordinate y k⌋,?_⟩
    have he : coordinate k p+(⌊realCoordinate y k⌋:ℤ)=realCoordinate y k := by
      have h := congrArg (fun q : ℝ × ℝ => realCoordinate q k) hy
      have hh : coordinate k p=Int.fract (realCoordinate y k) := by fin_cases k <;> exact h
      rw [hh]
      exact sub_add_cancel _ _
    rw [he]
    exact hcell k
  change p ∈ (spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper)).val
  rw [spatialTranslate_coordinateRectangle]
  exact ⟨hh 0,hh 1⟩

theorem mem_inwardMargin_of_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ)
    (hboundary : ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
      ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k)
    (hnearB : ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon)
    (p : GenericSquare a)
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.inwardMargin t u z).val := by
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hpM := C.mem_marginPolygon_of_planar hr.2 t u p p.val hy hcell
  have hgate k : p ∈ (C.inwardGate t u z k).val := by
    by_cases hzero : realCoordinate z k=0
    · simp only [inwardGate,ite_eq_left hzero]
      have hd := C.positiveDecision_planar hr t u (axisDirection k)
        (hnearB k (Or.inl hzero)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
      rw [integralCutForm_axis,hboundary k (Or.inl hzero),hzero] at hd
      apply hd.mpr
      have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
      rw [haxis]
      exact (coordinate_bounds k p).1
    · by_cases hone : realCoordinate z k=1
      · simp only [inwardGate,ite_eq_right hzero,ite_eq_left hone]
        have hd := C.positiveDecision_planar hr t u (axisDirection k)
          (hnearB k (Or.inr hone)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
        rw [integralCutForm_axis,hboundary k (Or.inr hone),hone] at hd
        apply (not_congr hd).mpr
        have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
        rw [haxis]
        exact not_le_of_gt (coordinate_bounds k p).2
      · simp [inwardGate,hzero,hone,wholePolygon]
  exact ⟨⟨hpM,hgate 0⟩,hgate 1⟩

end ConcurrentGeometry
end InwardMargins

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {ι : Type*}

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)
theorem neighborhood : C.InwardChartNeighborhood T.vertex T.offset z := T.property.1
theorem active_anchor : C.InwardChartAnchor T.vertex T.offset j c z := T.property.2.1
theorem active_bound : C.InwardChartBound T.vertex T.offset j c z := T.property.2.2.1
theorem boundary_anchor : C.InwardChartBoundaryAnchor T.vertex T.offset z := T.property.2.2.2.1
theorem boundary_bound : C.InwardChartBoundaryBound T.vertex T.offset z := T.property.2.2.2.2
end InwardChart

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem canonical_mem (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    p ∈ (C.inwardMargin T.vertex T.offset z).val :=
  C.mem_inwardMargin_of_planar hr T.vertex T.offset z T.boundary_anchor T.boundary_bound p
    (fun k => ⟨(T.neighborhood p.val hp k).1.le,(T.neighborhood p.val hp k).2⟩)

theorem local_decisions_eq (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p=
      polygonAssignment (localCutFamily j c z) p := by
  classical
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hcell k := (T.neighborhood p.val hp k).imp le_of_lt le_of_lt
  funext i
  apply decide_eq_decide.mpr
  by_cases hi : cutForm a (j i) z=ordinary (c i)
  · have hd := C.positiveDecision_planar hr T.vertex T.offset (j i) (T.active_bound i hi) p p.val hy hcell
    rw [T.active_anchor i hi] at hd
    simp only [localDecision,localCutFamily,ite_eq_left hi]
    change (p ∉ (C.positiveDecision T.vertex T.offset (j i)).val) ↔ cutForm a (j i) p.val<ordinary (c i)
    exact (not_congr hd).trans not_le
  · simp only [localDecision,localCutFamily,ite_eq_right hi]

theorem polygons_locally_eq [Finite ι] {κ : Type*}
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (R : κ → polygonAlgebra a)
    (hR : ∀ k, ResolvedBy (fun i => halfPlane a (j i) (c i)) (R k).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧ ∀ p : GenericSquare a, p.val ∈ N →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧ ∀ k, p ∈ (T.polygons R k).val ↔ p ∈ (R k).val := by
  obtain ⟨O,hO,hz,hlocal⟩ := localPolygonFamily_locally_eq j c z R hR
  refine ⟨O ∩ Metric.ball z (C.epsilon/2),hO.inter Metric.isOpen_ball,
    ⟨hz,by simp only [Metric.mem_ball,dist_self]; linarith [C.positive]⟩,?_⟩
  intro p hp
  refine ⟨T.canonical_mem hr p hp.2,fun k => ?_⟩
  have he := T.local_decisions_eq hr p hp.2
  change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
    polygonFormalMask (fun i => cutPolygon a (j i) (c i)) (R k) ↔ _
  rw [he]
  exact hlocal p hp.1 k

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConcurrentCoordinateGates
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
section ConcurrentCoordinateGates
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrentCoordinates_eq (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    A.concurrentCoordinates t u=fun i =>
      (coordinateTestIndex (Sum.elim id Prod.fst i),
        Sum.elim (fun k => u+A.geometry.anchors t (axisDirection k))
          (fun k => u+(coordinateWindowPrimitives A.geometry.window A.geometry.start k).2) i) := by
  funext i
  cases i <;> rfl

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_margin_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.marginPolygon t u).val := by
  intro x y hh
  apply translatedTemplate_resolved (coordinateWindowPrimitives A.geometry.window A.geometry.start)
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
    (A.geometry.margin_resolved t) u x y
  intro i
  exact hh (Sum.inr i)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_positive_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (k : Fin 2) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.positiveDecision t u (axisDirection k)).val := by
  intro x y hh
  exact hh (Sum.inl k)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_inward_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.inwardMargin t u z).val := by
  intro x y hh
  have hgate k : x ∈ (A.geometry.inwardGate t u z k).val ↔ y ∈ (A.geometry.inwardGate t u z k).val := by
    dsimp only [ConcurrentGeometry.inwardGate]
    split_ifs
    · exact A.coordinate_positive_resolved t u k x y hh
    · exact not_congr (A.coordinate_positive_resolved t u k x y hh)
    · exact Iff.rfl
  exact and_congr (and_congr (A.coordinate_margin_resolved t u x y hh) (hgate 0)) (hgate 1)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem coordinate_localDecision_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (k : Fin 2) (c : CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val)
      (A.geometry.localDecision t u z (axisDirection k) c).val := by
  intro x y hh
  dsimp only [ConcurrentGeometry.localDecision]
  split_ifs
  · exact not_congr (A.coordinate_positive_resolved t u k x y hh)
  · exact Iff.rfl
  · exact Iff.rfl

end InitialCoverSystem.PatchAtlas
end ConcurrentCoordinateGates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_InwardTemplateResolutions
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
section InwardTemplateResolutions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_margin_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.marginPolygon t u).val := by
  intro x y hh
  exact translatedTemplate_resolved (Sum.elim
    (fun j : Fin 4 => (⟨j.val+1,by omega⟩,A.geometry.anchors t j))
    (coordinateWindowPrimitives A.geometry.window A.geometry.start))
    (coordinateRectangle a (A.geometry.margins t).lower (A.geometry.margins t).upper)
    (fun x y hh => A.geometry.margin_resolved t x y (fun i => hh (Sum.inr i))) u x y hh

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_positive_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (j : Fin 4) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.positiveDecision t u j).val := by
  intro x y hh
  exact hh (Sum.inl j)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_inward_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.inwardMargin t u z).val := by
  intro x y hh
  have hgate k : x ∈ (A.geometry.inwardGate t u z k).val ↔ y ∈ (A.geometry.inwardGate t u z k).val := by
    dsimp only [ConcurrentGeometry.inwardGate]
    split_ifs
    · exact A.concurrent_positive_resolved t u (axisDirection k) x y hh
    · exact not_congr (A.concurrent_positive_resolved t u (axisDirection k) x y hh)
    · exact Iff.rfl
  exact and_congr (and_congr (A.concurrent_margin_resolved t u x y hh) (hgate 0)) (hgate 1)

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem concurrent_localDecision_resolved (t : VertexType (commonVertexDenominator a))
    (u : CutRing × CutRing) (z : ℝ × ℝ) (j : Fin 4) (c : CutRing) :
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives t u) i).val)
      (A.geometry.localDecision t u z j c).val := by
  intro x y hh
  dsimp only [ConcurrentGeometry.localDecision]
  split_ifs
  · exact not_congr (A.concurrent_positive_resolved t u j x y hh)
  · exact Iff.rfl
  · exact Iff.rfl

end InitialCoverSystem.PatchAtlas

theorem polygonBooleanPullback_resolved {a : ℕ} {ι κ : Type*} [Finite κ]
    (U : ι → polygonAlgebra a) (V : κ → polygonAlgebra a)
    (h : ∀ i, ResolvedBy (fun j => (U j).val) (V i).val) (S : Set (κ → Bool)) :
    ResolvedBy (fun j => (U j).val) (polygonBooleanPullback V S).val := by
  intro x y hxy
  have he : polygonAssignment V x=polygonAssignment V y :=
    (polygonAssignment_eq_iff V x y).mpr (fun i => h i x y hxy)
  change polygonAssignment V x ∈ S ↔ polygonAssignment V y ∈ S
  rw [he]

end InwardTemplateResolutions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ActiveClippedModelActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
theorem inward_model_resolved {ι κ : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : A.geometry.InwardChart j c z) (R : κ → polygonAlgebra a) (i : κ) :
    ResolvedBy (fun e => (primitiveTests (a := a) (r := r) (A.concurrentPrimitives T.vertex T.offset) e).val)
      (T.polygons R i).val :=
  polygonBooleanPullback_resolved _ _
    (fun e => A.concurrent_localDecision_resolved T.vertex T.offset z (j e) (c e)) _

end InitialCoverSystem.PatchAtlas

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem coordinate_concurrent_action (hlarge : 20 ≤ m+1)
    (d : Fin 2) (v : CutRing × CutRing)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (A.concurrentCoordinates t u) i).val) V.val)
    (n : ℕ) (q : Fin 2 → ℤ) (W : polygonAlgebra a)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val)
    (he : spatialTranslate v (coordinatePrimitive a d) ⊓ W=V ⊓ W)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (x : BoundedRelationCover M (alternatingGenerator a r m hm)) (hx : x ∈ f.range) :
    A.primitiveStar (by omega) (coordinateTestIndex d,v) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (coordinateTestIndex d,v) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) V
      (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives t u) (A.concurrentLaw t u) V
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let P := translatedTemplate (initialPatchPrimitives r A.geometry.mesh) v
  let h := fun J (_ : J.card ≤ 15) b hb => A.initial v J b hb
  let R : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (coordinateTestIndex d,v)
  let hR := fun J (_ : J.card ≤ 15) b hb =>
    B.coordinateFamilyLaw_all A.rectangles.rectangles (fun _ : Unit => d) (fun _ => v) J b hb
  have horig := B.fullGeometricSector_shared_primitive (by omega) P R (Sum.inl (coordinateTestIndex d)) ()
    (by simp [P,R,translatedTemplate,initialPatchPrimitives]) h hR
    (spatialTranslate v (coordinatePrimitive a d))
    (by intro y z hh; simpa only [P,primitiveTests,primitiveFamilyTests,translatedTemplate,
      initialPatchPrimitives,Sum.elim_inl,add_zero,initialTest_coordinate] using hh ())
  let J : Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) → Fin 2 := Sum.elim id Prod.fst
  let Z : Sum (Fin 2) (Fin 2 × Fin (A.geometry.window-1)) → CutRing × CutRing :=
    Sum.elim (fun k => u+A.geometry.anchors t (axisDirection k))
      (fun k => u+(coordinateWindowPrimitives A.geometry.window A.geometry.start k).2)
  let Q := fun i => (coordinateTestIndex (J i),Z i)
  let hQ := fun K (_ : K.card ≤ 15) b hb => B.coordinateFamilyLaw_all A.rectangles.rectangles J Z K b hb
  have hQe : Q=A.concurrentCoordinates t u := (A.concurrentCoordinates_eq t u).symm
  have hv : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    rw [hQe]; exact hV
  have htarget := B.fullGeometricSector_subfamily (by omega) (A.concurrentPrimitives t u) Q
    A.concurrentCoordinateEmbedding (by rw [hQe]; rfl) (A.concurrentLaw t u) hQ V hv
  change B.fullGeometricSector (by omega) P h (spatialTranslate v (initialTest a r (coordinateTestIndex d)))
    (universalMap (subtypeAlternatingHom I.val) s)*x*
    (B.fullGeometricSector (by omega) P h (spatialTranslate v (initialTest a r (coordinateTestIndex d)))
      (universalMap (subtypeAlternatingHom I.val) s))⁻¹ = _
  rw [initialTest_coordinate,horig,← htarget]
  exact B.coordinate_charts_action hlarge A.rectangles.rectangles (fun _ : Unit => d) (fun _ => v)
    J Z _ V W (fun y z hh => by simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hh ())
    hv n q hW he f hf hc I s x hx

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateModels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section CoordinateModels

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem coordinate_model_action_neighborhood_oai {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ) (G : CoordinateGerm a d u z)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : ι) (hlo : j lo=axisDirection d ∧ c lo=G.lower)
    (hhi : j hi=axisDirection d ∧ c hi=G.upper)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i)) (spatialTranslate u (coordinatePrimitive a d)).val) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ n q (W : polygonAlgebra a),
      ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (coordinateWindowPrimitives n q) i).val) W.val →
      (∀ p : GenericSquare a, p ∈ W.val → p.val ∈ N) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q W) →
      ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
      ∀ x ∈ f.range,
      A.primitiveStar (by omega) (coordinateTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
        (A.primitiveStar (by omega) (coordinateTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ())
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
          (T.polygons (fun _ : Unit => spatialTranslate u (coordinatePrimitive a d)) ())
            (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  let R : Unit → polygonAlgebra a := fun _ => spatialTranslate u (coordinatePrimitive a d)
  obtain ⟨N,hN,hz,hlocal⟩ := T.polygons_locally_eq hr R (fun _ => hR)
  let V : polygonAlgebra a := (A.geometry.localDecision T.vertex T.offset z (j lo) (c lo))ᶜ ⊓
    A.geometry.localDecision T.vertex T.offset z (j hi) (c hi)
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (A.concurrentCoordinates T.vertex T.offset) i).val) V.val := by
    intro p q hh
    apply and_congr
    · exact not_congr (by simpa only [hlo.1] using
        A.coordinate_localDecision_resolved T.vertex T.offset z d (c lo) p q hh)
    · simpa only [hhi.1] using A.coordinate_localDecision_resolved T.vertex T.offset z d (c hi) p q hh
  have he (p : GenericSquare a) (hp : p ∈ (A.geometry.inwardMargin T.vertex T.offset z).val) :
      p ∈ (T.polygons R ()).val ↔ p ∈ V.val :=
    G.model_formula T hr hz₁ hz₂ lo hi hlo hhi hR p hp
  have hrestrict : V ⊓ A.geometry.inwardMargin T.vertex T.offset z=
      T.polygons R () ⊓ A.geometry.inwardMargin T.vertex T.offset z := by
    apply Subtype.ext
    ext p
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases hp : p ∈ (A.geometry.inwardMargin T.vertex T.offset z).val
    · simp only [hp,and_true,he p hp]
    · simp only [hp,and_false]
  refine ⟨N,hN,hz,?_⟩
  intro n q W hW hWN f hf hc I s x hx
  have hinc : W ≤ A.geometry.inwardMargin T.vertex T.offset z := fun p hp => (hlocal p (hWN p hp)).1
  have heW : spatialTranslate u (coordinatePrimitive a d) ⊓ W=V ⊓ W := by
    apply Subtype.ext
    ext p
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases hp : p ∈ W.val
    · have hh := (hlocal p (hWN p hp)).2 ()
      simpa only [hp,and_true] using hh.symm.trans (he p (hinc hp))
    · simp only [hp,and_false]
  apply (A.coordinate_concurrent_action hlarge d u T.vertex T.offset V hV n q W hW heW f hf hc I s x hx).trans
  exact B.chart_action_transfer hlarge _ (A.concurrentLaw T.vertex T.offset) V (T.polygons R ()) _
    (fun p q hh => hV p q (fun i => hh (A.concurrentCoordinateEmbedding i)))
    (A.inward_model_resolved T R ()) (A.concurrent_inward_resolved T.vertex T.offset z) hrestrict f hf
    (A.coordinate_control_inward_gate hlarge T.vertex T.offset _ (A.coordinate_inward_resolved T.vertex T.offset z)
      n q W hW hinc f hf hc) I s x hx

end InitialCoverSystem.PatchAtlas
end CoordinateModels

end SimpleAmenable

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.coordinate_model_action_neighborhood_oai.{u_1}
