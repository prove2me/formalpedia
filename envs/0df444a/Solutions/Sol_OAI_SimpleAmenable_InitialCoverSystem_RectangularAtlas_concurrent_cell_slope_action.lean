-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:03:03.899059+00:00
-- url     : https://prove2.me/submissions/c9101749-d8b2-4f40-82f4-fd027c74a208

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_RectangularAtlas_slope_line_action

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_ConcurrentDenominators
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

section VertexResidues

theorem cut_residue_decomposition (D : ℕ) (z : CutRing) :
    z = cutResidue D z + (D : CutRing)*cutQuotient D z := by
  ext <;> simp [cutResidue,cutQuotient,Int.emod_add_mul_ediv]

theorem cutResidue_exists_finite {D : ℕ} (hD : 0<D) (z : CutRing) :
    ∃ t : Fin D × Fin D, cutResidue D z=finiteCutResidue D t := by
  have hDi : (0 : ℤ)<D := by exact_mod_cast hD
  let p : Fin D := ⟨(z.re % (D : ℤ)).toNat,by
    have h := Int.emod_lt_of_pos z.re hDi
    have hn := Int.emod_nonneg z.re (ne_of_gt hDi)
    omega⟩
  let q : Fin D := ⟨(z.im % (D : ℤ)).toNat,by
    have h := Int.emod_lt_of_pos z.im hDi
    have hn := Int.emod_nonneg z.im (ne_of_gt hDi)
    omega⟩
  refine ⟨⟨p,q⟩,?_⟩
  ext <;> simp [cutResidue,finiteCutResidue,p,q,Int.emod_nonneg _ (ne_of_gt hDi)]

theorem denominated_vertex_normal_form {D : ℕ} (hD : 0<D)
    (z : ℝ × ℝ) (u v : CutRing)
    (hu : ordinary u=(D : ℝ)*z.1) (hv : ordinary v=(D : ℝ)*z.2) :
    ∃ t : (Fin D × Fin D) × (Fin D × Fin D), ∃ x y : CutRing,
      z=vertexRepresentative D t+(ordinary x,ordinary y) := by
  obtain ⟨p,hp⟩ := cutResidue_exists_finite hD u
  obtain ⟨q,hq⟩ := cutResidue_exists_finite hD v
  have hd : (D : ℝ)≠0 := by exact_mod_cast ne_of_gt hD
  have hx := congrArg ordinary (cut_residue_decomposition D u)
  have hy := congrArg ordinary (cut_residue_decomposition D v)
  simp only [map_add,map_mul,map_natCast,hp,hq,hu,hv] at hx hy
  refine ⟨(p,q),cutQuotient D u,cutQuotient D v,?_⟩
  apply Prod.ext
  · change z.1=ordinary (finiteCutResidue D p)/(D : ℝ)+ordinary (cutQuotient D u)
    apply (mul_left_cancel₀ hd)
    rw [mul_add,mul_div_cancel₀ _ hd]
    exact hx
  · change z.2=ordinary (finiteCutResidue D q)/(D : ℝ)+ordinary (cutQuotient D v)
    apply (mul_left_cancel₀ hd)
    rw [mul_add,mul_div_cancel₀ _ hd]
    exact hy

theorem all_intersections_finite_templates {a : ℕ} (ha : 0<a)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z=ordinary c) (hj : cutForm a j z=ordinary d) :
    ∃ t : (Fin (commonVertexDenominator a) × Fin (commonVertexDenominator a)) ×
        (Fin (commonVertexDenominator a) × Fin (commonVertexDenominator a)),
      ∃ x y : CutRing,
        z=vertexRepresentative (commonVertexDenominator a) t+(ordinary x,ordinary y) := by
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha i j hij c d z hi hj
  exact denominated_vertex_normal_form (commonVertexDenominator_pos ha) z u v hu hv

end VertexResidues

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentAnchors
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
section ConcurrentAnchors

theorem representative_line_allowable (a D : ℕ) (t : VertexType D)
    (u : CutRing × CutRing) (j : Fin 4) (c : CutRing) (z : ℝ × ℝ)
    (hz : z=vertexRepresentative D t+(ordinary u.1,ordinary u.2))
    (hc : cutForm a j z=ordinary c) : AllowableVertexLine a (vertexRepresentative D t) j := by
  refine ⟨c-integralCutForm a j u,?_⟩
  rw [hz,cutForm_add,cutForm_ordinary] at hc
  rw [map_sub]
  linarith

theorem translated_vertex_anchors (a D : ℕ) {ε : ℝ}
    (U : VertexType D → Fin 4 → CutRing × CutRing)
    (hU : ∀ t j, AllowableVertexLine a (vertexRepresentative D t) j →
      cutForm a j (vertexRepresentative D t)=ordinary (integralCutForm a j (U t j)) ∧
      dist (ordinary (U t j).1,ordinary (U t j).2) (vertexRepresentative D t)<ε)
    (t : VertexType D) (u : CutRing × CutRing) (j : Fin 4) (c : CutRing) (z : ℝ × ℝ)
    (hz : z=vertexRepresentative D t+(ordinary u.1,ordinary u.2))
    (hc : cutForm a j z=ordinary c) :
    integralCutForm a j (u+U t j)=c ∧
      dist (ordinary (u+U t j).1,ordinary (u+U t j).2) z<ε := by
  obtain ⟨he,hd⟩ := hU t j (representative_line_allowable a D t u j c z hz hc)
  constructor
  · apply ordinary_injective
    rw [← cutForm_ordinary]
    have hpair : (ordinary (u+U t j).1,ordinary (u+U t j).2)=
        (ordinary (U t j).1,ordinary (U t j).2)+(ordinary u.1,ordinary u.2) := by
      ext <;> simp [add_comm]
    rw [hpair,cutForm_add,cutForm_ordinary,← he,← cutForm_add,← hz,hc]
  · have hpair : (ordinary (u+U t j).1,ordinary (u+U t j).2)=
        (ordinary (U t j).1,ordinary (U t j).2)+(ordinary u.1,ordinary u.2) := by
      ext <;> simp [add_comm]
    rwa [hpair,hz,dist_add_right]

end ConcurrentAnchors

section LineIntersectionBounds

theorem real_two_lines_intersect (A B C E c d : ℝ) (h : A*E-C*B ≠ 0) :
    ∃ z : ℝ × ℝ, A*z.1+B*z.2=c ∧ C*z.1+E*z.2=d := by
  refine ⟨((c*E-d*B)/(A*E-C*B),(A*d-C*c)/(A*E-C*B)),?_,?_⟩ <;>
    dsimp only <;> rw [← mul_div_assoc, ← mul_div_assoc, ← add_div] <;>
      apply (div_eq_iff h).mpr <;> ring

theorem real_two_lines_distance_bound (A B C E c d : ℝ) (h : A*E-C*B ≠ 0)
    (z p : ℝ × ℝ) (hz : A*z.1+B*z.2=c) (hz' : C*z.1+E*z.2=d)
    (δ : ℝ) (hδ : 0≤δ)
    (hp : |c-(A*p.1+B*p.2)| ≤ δ) (hp' : |d-(C*p.1+E*p.2)| ≤ δ) :
    dist z p ≤ ((|A| + |B| + |C| + |E|)/|A*E-C*B|)*δ := by
  have hd : 0 < |A*E-C*B| := abs_pos.mpr h
  have hx : (A*E-C*B)*(z.1-p.1)=E*(c-(A*p.1+B*p.2))-B*(d-(C*p.1+E*p.2)) := by
    linear_combination E*hz-B*hz'
  have hy : (A*E-C*B)*(z.2-p.2)=A*(d-(C*p.1+E*p.2))-C*(c-(A*p.1+B*p.2)) := by
    linear_combination A*hz'-C*hz
  have hx' : |A*E-C*B| * |z.1-p.1| ≤ (|E| + |B|)*δ := by
    rw [← abs_mul,hx]
    calc
      _ ≤ |E*(c-(A*p.1+B*p.2))| + |B*(d-(C*p.1+E*p.2))| := abs_sub _ _
      _ ≤ |E| * δ+|B| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
      _ = _ := by ring
  have hy' : |A*E-C*B| * |z.2-p.2| ≤ (|A| + |C|)*δ := by
    rw [← abs_mul,hy]
    calc
      _ ≤ |A*(d-(C*p.1+E*p.2))| + |C*(c-(A*p.1+B*p.2))| := abs_sub _ _
      _ ≤ |A| * δ+|C| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
      _ = _ := by ring
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  rw [div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg A,abs_nonneg C]
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg B,abs_nonneg E]

theorem real_lineDet_ne_zero {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j) :
    ordinary (lineNormal a i).1*ordinary (lineNormal a j).2-
      ordinary (lineNormal a j).1*ordinary (lineNormal a i).2 ≠ 0 := by
  have hh := ordinary_injective.ne (lineDet_ne_zero ha i j hij)
  simpa only [lineDet,map_sub,map_mul,map_zero] using hh

theorem allowable_lines_intersect {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j)
    (c d : CutRing) : ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d := by
  obtain ⟨z,hz,hz'⟩ := real_two_lines_intersect _ _ _ _ (ordinary c) (ordinary d)
    (real_lineDet_ne_zero ha i j hij)
  exact ⟨z,by rwa [cutForm_normal],by rwa [cutForm_normal]⟩

end LineIntersectionBounds

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

section CellLineIntersections

theorem linear_form_dist_bound (A B : ℝ) (x y : ℝ × ℝ) :
    |(A*x.1+B*x.2)-(A*y.1+B*y.2)| ≤ (|A|+|B|)*dist x y := by
  have hx : |x.1-y.1| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have hy : |x.2-y.2| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |A*(x.1-y.1)+B*(x.2-y.2)| := by congr 1; ring
    _ ≤ |A*(x.1-y.1)|+|B*(x.2-y.2)| := abs_add_le _ _
    _ ≤ |A| *dist x y+|B| *dist x y := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = _ := by ring

theorem crossing_level_bound (A B c δ : ℝ) (p x y : ℝ × ℝ)
    (hx : A*x.1+B*x.2 ≤ c) (hy : c≤A*y.1+B*y.2)
    (hpx : dist p x≤δ) (hpy : dist p y≤δ) :
    |c-(A*p.1+B*p.2)| ≤ (|A|+|B|)*δ := by
  have h₁ := (linear_form_dist_bound A B x p).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hpx) (by positivity))
  have h₂ := (linear_form_dist_bound A B y p).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hpy) (by positivity))
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).2
  apply abs_le.mpr
  constructor <;> linarith

theorem line_point_in_box (A B c : ℝ) (L V : Fin 2 → ℝ) (x y : ℝ × ℝ)
    (hx : ∀ j, L j ≤ realCoordinate x j ∧ realCoordinate x j≤V j)
    (hy : ∀ j, L j ≤ realCoordinate y j ∧ realCoordinate y j≤V j)
    (hcx : A*x.1+B*x.2 ≤ c) (hcy : c≤A*y.1+B*y.2) :
    ∃ z : ℝ × ℝ, A*z.1+B*z.2=c ∧
      ∀ j, L j ≤ realCoordinate z j ∧ realCoordinate z j≤V j := by
  let f : ℝ → ℝ := fun t => A*((1-t)*x.1+t*y.1)+B*((1-t)*x.2+t*y.2)
  have hf : Continuous f := by unfold f; fun_prop
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hf.continuousOn
    (show c ∈ Set.Icc (f 0) (f 1) from by simpa [f] using And.intro hcx hcy)
  refine ⟨((1-t)*x.1+t*y.1,(1-t)*x.2+t*y.2),he,?_⟩
  intro j
  have hx' := hx j
  have hy' := hy j
  have hform : realCoordinate ((1-t)*x.1+t*y.1,(1-t)*x.2+t*y.2) j=
      (1-t)*realCoordinate x j+t*realCoordinate y j := by fin_cases j <;> rfl
  rw [hform]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.1),
    mul_nonneg ht.1 (sub_nonneg.mpr hy'.1),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hx'.2),
    mul_nonneg ht.1 (sub_nonneg.mpr hy'.2)]

end CellLineIntersections

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_UniformConcurrentMesh
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
section UniformConcurrentMesh

theorem lineIntersectionCoefficient_le (a : ℕ) (i j : Fin 4) :
    lineIntersectionCoefficient a i j≤lineIntersectionConstant a := by
  have h₁ := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
    lineIntersectionCoefficient_nonneg a i k) (Finset.mem_univ j)
  have h₂ := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 4))) =>
    Finset.sum_nonneg (fun l (_ : l ∈ (Finset.univ : Finset (Fin 4))) =>
      lineIntersectionCoefficient_nonneg a k l)) (Finset.mem_univ i)
  unfold lineIntersectionConstant
  linarith

end UniformConcurrentMesh

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

theorem realCoordinate_dist_le (x y : ℝ × ℝ) (j : Fin 2) :
    |realCoordinate x j-realCoordinate y j| ≤ dist x y := by
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem realCoordinate_add (x y : ℝ × ℝ) (j : Fin 2) :
    realCoordinate (x+y) j=realCoordinate x j+realCoordinate y j := by
  fin_cases j <;> rfl

theorem realCoordinate_ordinary (u : CutRing × CutRing) (j : Fin 2) :
    realCoordinate (ordinary u.1,ordinary u.2) j=ordinary (pointCoordinate u j) := by
  fin_cases j <;> rfl

namespace VertexMargin
variable {z : ℝ × ℝ} {ε : ℝ} (V : VertexMargin z ε)

theorem translated_inner (u : CutRing × CutRing) (x : ℝ × ℝ)
    (hx : dist x (z+(ordinary u.1,ordinary u.2))≤ε) (j : Fin 2) :
    ordinary (V.lower j+pointCoordinate u j) < realCoordinate x j ∧
    realCoordinate x j<ordinary (V.upper j+pointCoordinate u j) := by
  have hh := (abs_le.mp ((realCoordinate_dist_le x (z+(ordinary u.1,ordinary u.2)) j).trans hx))
  rw [realCoordinate_add,realCoordinate_ordinary] at hh
  rw [map_add,map_add]
  have h₁ := V.lower_inner j
  have h₂ := V.upper_inner j
  constructor <;> linarith

theorem translated_outer (u b : CutRing × CutRing) (x : ℝ × ℝ)
    (hb : dist (ordinary b.1,ordinary b.2) (z+(ordinary u.1,ordinary u.2))<ε)
    (hx : ∀ j, ordinary (V.lower j+pointCoordinate u j) ≤ realCoordinate x j ∧
      realCoordinate x j≤ordinary (V.upper j+pointCoordinate u j)) (j : Fin 2) :
    |realCoordinate x j-ordinary (pointCoordinate b j)|<3*ε := by
  have hh := (abs_lt.mp ((realCoordinate_dist_le (ordinary b.1,ordinary b.2)
      (z+(ordinary u.1,ordinary u.2)) j).trans_lt hb))
  rw [realCoordinate_add,realCoordinate_ordinary,realCoordinate_ordinary] at hh
  have hk := hx j
  rw [map_add,map_add] at hk
  have h₁ := V.lower_outer j
  have h₂ := V.upper_outer j
  apply abs_lt.mpr
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

theorem mesh_small : 200/(C.mesh:ℝ)<C.epsilon := by
  have h := mul_le_mul_of_nonneg_right (lineIntersectionConstant_ge_one a)
    (show 0 ≤ 200/(C.mesh:ℝ) by positivity)
  simpa only [one_mul] using h.trans_lt C.mesh_fine

end ConcurrentGeometry

end ConcurrentGeometry

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

theorem windowRectangle_closed_intersection_near {a : ℕ} (ha : 0<a)
    (n : ℕ) (hn : 201 ≤ n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (x y u v : GenericSquare a)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hu : u ∈ (windowRectangle a n q cell).val)
    (hv : v ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x) ≤ ordinary c)
    (hcy : ordinary c ≤ cutForm a i (windowPlanarLift q y))
    (hdu : cutForm a j (windowPlanarLift q u) ≤ ordinary d)
    (hdv : ordinary d ≤ cutForm a j (windowPlanarLift q v)) :
    ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d ∧
      ∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut n (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut n (q k) (cell k).succ)) →
        dist z p ≤ lineIntersectionConstant a*(200/(n:ℝ)) := by
  obtain ⟨z,hz,hz'⟩ := allowable_lines_intersect ha i j hij c d
  refine ⟨z,hz,hz',fun p hp => ?_⟩
  have hc (t : GenericSquare a) (ht : t ∈ (windowRectangle a n q cell).val) :
      dist p (windowPlanarLift q t) ≤ 200/(n:ℝ) := by
    apply closedWindow_diameter n q cell p (windowPlanarLift q t) hp
    intro k
    exact ⟨((windowRectangle_mem n hn q cell t).mp ht k).1,
      ((windowRectangle_mem n hn q cell t).mp ht k).2.le⟩
  have h₁ := crossing_level_bound (ordinary (lineNormal a i).1) (ordinary (lineNormal a i).2)
    (ordinary c) (200/(n:ℝ)) p (windowPlanarLift q x) (windowPlanarLift q y)
    (by simpa only [cutForm_normal] using hcx) (by simpa only [cutForm_normal] using hcy)
    (hc x hx) (hc y hy)
  have h₂ := crossing_level_bound (ordinary (lineNormal a j).1) (ordinary (lineNormal a j).2)
    (ordinary d) (200/(n:ℝ)) p (windowPlanarLift q u) (windowPlanarLift q v)
    (by simpa only [cutForm_normal] using hdu) (by simpa only [cutForm_normal] using hdv)
    (hc u hu) (hc v hv)
  have hδ : 0 ≤ 200/(n:ℝ) := by positivity
  have hm₁ := mul_le_mul_of_nonneg_right (le_max_left
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hm₂ := mul_le_mul_of_nonneg_right (le_max_right
    (|ordinary (lineNormal a i).1|+|ordinary (lineNormal a i).2|)
    (|ordinary (lineNormal a j).1|+|ordinary (lineNormal a j).2|)) hδ
  have hh := real_two_lines_distance_bound _ _ _ _ (ordinary c) (ordinary d)
    (real_lineDet_ne_zero ha i j hij) z p (by simpa only [cutForm_normal] using hz)
    (by simpa only [cutForm_normal] using hz') _ (by positivity) (h₁.trans hm₁) (h₂.trans hm₂)
  have hh' : dist z p ≤ lineIntersectionCoefficient a i j*(200/(n:ℝ)) := by
    simpa only [lineIntersectionCoefficient,lineDet,map_sub,map_mul,mul_assoc] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_right (lineIntersectionCoefficient_le a i j) hδ)

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem crossing_cell_template (ha : 0<a) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing)
    (x y v w : GenericSquare a)
    (hx : x ∈ (windowRectangle a C.mesh q cell).val)
    (hy : y ∈ (windowRectangle a C.mesh q cell).val)
    (hv : v ∈ (windowRectangle a C.mesh q cell).val)
    (hw : w ∈ (windowRectangle a C.mesh q cell).val)
    (hcx : cutForm a i (windowPlanarLift q x) ≤ ordinary c)
    (hcy : ordinary c ≤ cutForm a i (windowPlanarLift q y))
    (hdv : cutForm a j (windowPlanarLift q v) ≤ ordinary d)
    (hdw : ordinary d ≤ cutForm a j (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      integralCutForm a i (u+C.anchors t i)=c ∧
      integralCutForm a j (u+C.anchors t j)=d ∧
      (∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
        ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate p k ∧
          realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      (∀ b ∈ ({i,j} : Set (Fin 4)), ∀ p : ℝ × ℝ,
        (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
        ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) := by
  obtain ⟨z,hz,hz',hclose⟩ := windowRectangle_closed_intersection_near ha C.mesh C.mesh_large q cell
    i j hij c d x y v w hx hy hv hw hcx hcy hdv hdw
  obtain ⟨t,u₁,u₂,htu⟩ := all_intersections_finite_templates ha i j hij c d z hz hz'
  let u := (u₁,u₂)
  have hi := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec t u i c z htu hz
  have hj := translated_vertex_anchors a (commonVertexDenominator a) C.anchors C.anchors_spec t u j d z htu hz'
  refine ⟨t,u,hi.1,hj.1,?_,?_⟩
  · intro p hp k
    apply (C.margins t).translated_inner u p
    rw [← htu,dist_comm]
    exact ((hclose p hp).trans_lt C.mesh_fine).le
  · intro b hb p hp k
    have hb' : b=i ∨ b=j := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hb
    have hdist : dist (ordinary (u+C.anchors t b).1,ordinary (u+C.anchors t b).2)
        (vertexRepresentative (commonVertexDenominator a) t+(ordinary u.1,ordinary u.2))<C.epsilon := by
      rw [← htu]
      rcases hb' with rfl | rfl
      · exact hi.2
      · exact hj.2
    exact (C.margins t).translated_outer u (u+C.anchors t b) p hdist hp k

end ConcurrentGeometry
end ClosedCellTemplates

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

section ActualSlopeClassifier

theorem windowRectangle_crossing_line_point {a : ℕ}
    (n : ℕ) (hn : 201≤n) (q : Fin 2 → ℤ) (cell : Fin 2 → Fin n)
    (j : Fin 4) (c : CutRing) (x y : GenericSquare a)
    (hx : x ∈ (windowRectangle a n q cell).val)
    (hy : y ∈ (windowRectangle a n q cell).val)
    (hcx : cutForm a j (windowPlanarLift q x)≤ordinary c)
    (hcy : ordinary c ≤ cutForm a j (windowPlanarLift q y)) :
    ∃ z : ℝ × ℝ, cutForm a j z=ordinary c ∧ ∀ d,
      ordinary (windowCut n (q d) (cell d).castSucc) ≤ realCoordinate z d ∧
      realCoordinate z d≤ordinary (windowCut n (q d) (cell d).succ) := by
  rw [cutForm_normal] at hcx hcy
  obtain ⟨z,hz,hb⟩ := line_point_in_box (ordinary (lineNormal a j).1)
    (ordinary (lineNormal a j).2) (ordinary c)
    (fun d => ordinary (windowCut n (q d) (cell d).castSucc))
    (fun d => ordinary (windowCut n (q d) (cell d).succ))
    (windowPlanarLift q x) (windowPlanarLift q y)
    (fun d => ⟨((windowRectangle_mem n hn q cell x).mp hx d).1,
      ((windowRectangle_mem n hn q cell x).mp hx d).2.le⟩)
    (fun d => ⟨((windowRectangle_mem n hn q cell y).mp hy d).1,
      ((windowRectangle_mem n hn q cell y).mp hy d).2.le⟩) hcx hcy
  exact ⟨z,by rwa [cutForm_normal],hb⟩

end ActualSlopeClassifier

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConcurrentCellSlopeAction
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
section ConcurrentCellSlopeAction
namespace InitialCoverSystem.RectangularAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.RectangularAtlas) (C : ConcurrentGeometry a r)

theorem concurrent_cell_slope_action_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (ha : 0<a)
    (q : Fin 2 → ℤ) (cell : Fin 2 → Fin C.mesh)
    (d : Fin 2) (axis : Fin 4) (hne : slopeDirection d≠axis)
    (z : CutRing × CutRing) (c : CutRing)
    (hclip : ∀ k, -ordinary r ≤ ordinary (windowCut C.mesh (q k) (cell k).castSucc)-
        ordinary (pointCoordinate z k) ∧
      ordinary (windowCut C.mesh (q k) (cell k).succ)-ordinary (pointCoordinate z k) ≤ ordinary r)
    (x y v w : GenericSquare a)
    (hx : x ∈ (windowRectangle a C.mesh q cell).val)
    (hy : y ∈ (windowRectangle a C.mesh q cell).val)
    (hv : v ∈ (windowRectangle a C.mesh q cell).val)
    (hw : w ∈ (windowRectangle a C.mesh q cell).val)
    (hcx : cutForm a (slopeDirection d) (windowPlanarLift q x) ≤ ordinary (integralCutForm a (slopeDirection d) z))
    (hcy : ordinary (integralCutForm a (slopeDirection d) z) ≤ cutForm a (slopeDirection d) (windowPlanarLift q y))
    (hdv : cutForm a axis (windowPlanarLift q v) ≤ ordinary c)
    (hdw : ordinary c ≤ cutForm a axis (windowPlanarLift q w)) :
    ∃ t : VertexType (commonVertexDenominator a), ∃ u : CutRing × CutRing,
      integralCutForm a (slopeDirection d) (u+C.anchors t (slopeDirection d))=
        integralCutForm a (slopeDirection d) z ∧
      integralCutForm a axis (u+C.anchors t axis)=c ∧
      (∀ p : ℝ × ℝ,
        (∀ k, ordinary (windowCut C.mesh (q k) (cell k).castSucc) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary (windowCut C.mesh (q k) (cell k).succ)) →
        ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate p k ∧
          realCoordinate p k<ordinary ((C.margins t).upper k+pointCoordinate u k)) ∧
      (∀ b ∈ ({slopeDirection d,axis} : Set (Fin 4)), ∀ p : ℝ × ℝ,
        (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p k ∧
          realCoordinate p k ≤ ordinary ((C.margins t).upper k+pointCoordinate u k)) →
        ∀ k, |realCoordinate p k-ordinary (pointCoordinate (u+C.anchors t b) k)|<3*C.epsilon) ∧
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
        B.AlignedSmallSupported f →
        SmallControlled B.c f (B.windowSector (by omega) C.mesh (A.rectangles C.mesh) q
          (windowRectangle a C.mesh q cell)) →
        ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
          ∀ b ∈ f.range,
            A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
              A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s)*b*
                (A.slope (by omega) d (u+C.anchors t (slopeDirection d)) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨t,u,hline,haxis,hmargin,hclose⟩ := C.crossing_cell_template ha q cell
    (slopeDirection d) axis hne (integralCutForm a (slopeDirection d) z) c
    x y v w hx hy hv hw hcx hcy hdv hdw
  refine ⟨t,u,hline,haxis,hmargin,hclose,?_⟩
  let L := fun k => windowCut C.mesh (q k) (cell k).castSucc
  let V := fun k => windowCut C.mesh (q k) (cell k).succ
  have hLV (k) : ordinary (L k) ≤ ordinary (V k) :=
    (windowCut_strictMono C.mesh (q k) (Fin.castSucc_lt_succ (i := cell k))).le
  obtain ⟨z₀,hz₀,hz₀cell⟩ := windowRectangle_crossing_line_point C.mesh C.mesh_large q cell
    (slopeDirection d) (integralCutForm a (slopeDirection d) z) x y hx hy hcx hcy
  have hLcell : ∀ k, ordinary (L k) ≤ realCoordinate (ordinary (L 0),ordinary (L 1)) k ∧
      realCoordinate (ordinary (L 0),ordinary (L 1)) k ≤ ordinary (V k) := by
    intro k; fin_cases k <;> exact ⟨le_rfl,hLV _⟩
  have hVcell : ∀ k, ordinary (L k) ≤ realCoordinate (ordinary (V 0),ordinary (V 1)) k ∧
      realCoordinate (ordinary (V 0),ordinary (V 1)) k ≤ ordinary (V k) := by
    intro k; fin_cases k <;> exact ⟨hLV _,le_rfl⟩
  have hclip' : ∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate (u+C.anchors t (slopeDirection d)) k) ∧
      ordinary (V k)-ordinary (pointCoordinate (u+C.anchors t (slopeDirection d)) k) ≤ ordinary r := by
    intro k
    have hmL := fun l => (hmargin _ hLcell l).imp le_of_lt le_of_lt
    have hmV := fun l => (hmargin _ hVcell l).imp le_of_lt le_of_lt
    have h₁ := hclose (slopeDirection d) (by simp) _ hmL k
    have h₂ := hclose (slopeDirection d) (by simp) _ hmV k
    have hc₁ : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
    have hc₂ : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
    rw [hc₁] at h₁
    rw [hc₂] at h₂
    have hb₁ := (abs_lt.mp h₁).1
    have hb₂ := (abs_lt.mp h₂).2
    have hh := C.radius
    have hpos := C.positive
    constructor <;> linarith
  have hnear (k) : |ordinary (L k)-realCoordinate z₀ k| ≤ ordinary r/4 ∧
      |ordinary (V k)-realCoordinate z₀ k| ≤ ordinary r/4 := by
    have hh := hz₀cell k
    have hm := windowCut_mesh C.mesh (q k) (cell k)
    have he := C.mesh_small
    have hr' := C.radius
    have hpos := C.positive
    change ordinary (L k) ≤ realCoordinate z₀ k ∧ realCoordinate z₀ k ≤ ordinary (V k) at hh
    change ordinary (V k)-ordinary (L k) ≤ 200/(C.mesh:ℝ) at hm
    rw [abs_of_nonpos (by linarith : ordinary (L k)-realCoordinate z₀ k≤0),
      abs_of_nonneg (by linarith : 0≤ordinary (V k)-realCoordinate z₀ k)]
    constructor <;> linarith
  intro f hf hc I s b hb
  exact A.slope_line_action hlarge hr d z (u+C.anchors t (slopeDirection d)) hline.symm L V hLV
    hclip hclip' z₀ hz₀ hnear C.mesh q (windowRectangle_resolved C.mesh (by have hh := C.mesh_large; omega) q cell)
    f hf hc I s b hb

end InitialCoverSystem.RectangularAtlas
end ConcurrentCellSlopeAction

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action_oai := @OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.concurrent_cell_slope_action_oai
