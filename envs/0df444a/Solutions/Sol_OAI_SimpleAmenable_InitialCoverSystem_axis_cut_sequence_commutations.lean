-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:42:58.256346+00:00
-- url     : https://prove2.me/submissions/e5f59438-2f59-472d-8047-60e2e626409e

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_separated_old_rectangles_commute

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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowIntervals
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSectorCompatibility
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ControlCalculus
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem axisSector_supported (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val) :
    B.AlignedSmallSupported (B.axisSector hlarge n h j k hk p V) :=
  B.fullGeometricSector_supported hlarge _ _ V hV

end InitialCoverSystem
end SourceControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_Rectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section OldRectangles

namespace LabelledRectangle
variable {n : ℕ} (R : LabelledRectangle n)

theorem resolved (a : ℕ) (r : CutRing) :
    ResolvedBy (fun i => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n R.start) i).val) (R.polygon a).val := by
  have hl (j : Fin 2) : R.start j ≤ endpointLabel (R.lower j) ∧ endpointLabel (R.lower j) < R.start j+n := by
    have hh := R.lower_label j; have hh' := R.length_le j; omega
  have hv (j : Fin 2) : R.start j ≤ endpointLabel (R.upper j) ∧ endpointLabel (R.upper j) < R.start j+n := by
    have hh := R.upper_label j; have hh' := R.length_le j; omega
  intro x y he
  exact and_congr (coordinateLabelWindow_resolved n R.start 0 _ _ (hl 0) (hv 0) x y he)
    (coordinateLabelWindow_resolved n R.start 1 _ _ (hl 1) (hv 1) x y he)

end LabelledRectangle

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem rectangleCopy_supported (hlarge : 15 < m+1) {n : ℕ}
    (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n) :
    B.AlignedSmallSupported (B.rectangleCopy hlarge g R) :=
  B.fullGeometricSector_supported hlarge _ _ _ (R.resolved a r)

theorem rectangleCopy_axes_control (hlarge : 15 < m+1) {n : ℕ}
    (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n) (j : Fin 2) :
    SmallControlled B.c (B.rectangleCopy hlarge g R)
      (B.axisSector hlarge n g j (R.length j) (R.length_le j) (R.start j)
        (coordinateInterval a j (R.lower j) (R.upper j))) := by
  rw [B.axisSector_in_window hlarge n g j _ (R.length_le j) _ R.start le_rfl
    (by have hh := R.length_le j; omega) _
    (axisInterval_resolved j _ _ _ _ (R.lower_label j) (R.upper_label j))]
  apply B.fullGeometricSector_small_control
  fin_cases j
  · exact inf_le_left
  · exact inf_le_right

end InitialCoverSystem
end OldRectangles

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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem windowCell_pairwise_disjoint {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ) :
    Pairwise fun i k : Fin n => Disjoint (windowCell a j n q i).val (windowCell a j n q k).val := by
  intro i k hik
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hi := (windowCell_mem j n hn q i p).mp hp
  have hk := (windowCell_mem j n hn q k p).mp hp'
  rcases lt_or_gt_of_ne hik with hh | hh
  · have he := (windowCut_strictMono n q).monotone
      (show i.succ ≤ k.castSucc from by change i.val+1 ≤ k.val; change i.val < k.val at hh; omega)
    linarith
  · have he := (windowCut_strictMono n q).monotone
      (show k.succ ≤ i.castSucc from by change k.val+1 ≤ i.val; change k.val < i.val at hh; omega)
    linarith

end WindowCellPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CellGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section CellGeometry

theorem windowCell_axis_resolved {a : ℕ} {r : CutRing} (j : Fin 2) (n : ℕ) (hn : 0 < n) (q : ℤ) (i : Fin n) :
    ResolvedBy (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j n q) z).val) (windowCell a j n q i).val :=
  axisInterval_resolved j n q _ _ (windowCut_label n q hn i.castSucc) (windowCut_label n q hn i.succ)

end CellGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section FiniteSectorPartition
namespace ActualLawfulTable
variable {E H Q Ω κ : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_range_le_biUnion (W : κ → Set Ω) (S : Finset κ)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hd : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hdisjoint (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j) = W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he,T.sector_union hd]
    rintro x ⟨s,rfl⟩
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set Ω) (V : Set Ω)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j))
    (hcover : ∀ ω, ω ∈ V ↔ ∃ i, ω ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V = ⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext ω
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hcover ω
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hdisjoint _
    (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Fintype κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_partition_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (W : κ → polygonAlgebra a)
    (hW : ∀ i, ResolvedBy (fun z => (primitiveTests (a := a) (r := r) P z).val) (W i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (W i).val (W j).val)
    (hcover : ∀ p, p ∈ V.val ↔ ∃ i, p ∈ (W i).val) :
    (B.fullGeometricSector hlarge P h V).range ≤
      ⨆ i, (B.fullGeometricSector hlarge P h (W i)).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_range_le_partition
  · intro i j hij
    exact resolvedPolygonMask_disjoint _ (hW i) (hdisjoint hij)
  · intro ω
    constructor
    · rintro ⟨p,hp,hpV⟩
      obtain ⟨i,hi⟩ := (hcover p).mp hpV
      exact ⟨i,p,hp,hi⟩
    · rintro ⟨i,p,hp,hi⟩
      exact ⟨p,hp,(hcover p).mpr ⟨i,hi⟩⟩

end InitialCoverSystem

theorem commute_of_range_iSup {G X Y : Type*} [Group G] [Group X] [Group Y]
    {ι κ : Type*} (f : ι → X →* G) (g : κ → Y →* G)
    (hc : ∀ i j s t, Commute (f i s) (g j t))
    {x y : G} (hx : x ∈ ⨆ i, (f i).range) (hy : y ∈ ⨆ j, (g j).range) : Commute x y := by
  have hleft (j : κ) (t : Y) : (⨆ i, (f i).range) ≤ Subgroup.centralizer {g j t} := by
    apply iSup_le
    intro i z hz w hw
    obtain ⟨s,rfl⟩ := hz
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact (hc i j s t).eq.symm
  have hright : (⨆ j, (g j).range) ≤ Subgroup.centralizer {x} := by
    apply iSup_le
    intro j z hz w hw
    obtain ⟨t,rfl⟩ := hz
    obtain rfl := Set.mem_singleton_iff.mp hw
    exact (hleft j t hx _ (Set.mem_singleton _)).symm
  exact hright hy _ (Set.mem_singleton _)

end FiniteSectorPartition

section AxisCellSplitting

theorem axisCellRectangle_polygon {a n : ℕ} (d : Fin 2)
    (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) :
    (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i).polygon a =
      coordinateInterval a d u v ⊓ windowCell a (otherAxis d) l q i := by
  fin_cases d
  · rfl
  · change coordinateInterval a 0 _ _ ⊓ coordinateInterval a 1 u v =
      coordinateInterval a 1 u v ⊓ coordinateInterval a 0 _ _
    exact inf_comm _ _

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_range_cells (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 201 ≤ l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v)).range ≤
      ⨆ i : Fin l, (B.rectangleCopy hlarge g
        (axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i)).range := by
  let R := axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv
  let z : Fin 2 → ℤ := fun j => if j=d then p else q
  rw [B.axisSector_in_window hlarge n g d k hk p z
    (by simp [z]) (by simp [z]; omega) _ (axisInterval_resolved d k p u v hu hv)]
  change (B.fullGeometricSector hlarge (coordinateWindowPrimitives n z) _ _).range ≤ _
  apply B.fullGeometricSector_partition_range hlarge (coordinateWindowPrimitives n z)
    (fun I _ b hb => g I b hb z) (coordinateInterval a d u v) (fun i => (R i).polygon a)
  · intro i
    exact (R i).resolved a r
  · intro i j hij
    rw [axisCellRectangle_polygon,axisCellRectangle_polygon]
    exact (windowCell_pairwise_disjoint (a := a) (otherAxis d) l hlpos q hij).mono
      (Set.inter_subset_right) (Set.inter_subset_right)
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := windowCell_cover (a := a) (otherAxis d) l hlpos q x
      refine ⟨i,?_⟩
      rw [axisCellRectangle_polygon]
      exact ⟨hx,hi⟩
    · rintro ⟨i,hi⟩
      rw [axisCellRectangle_polygon] at hi
      exact hi.1

theorem axisCellRectangle_grid_control (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (hlpos : 0 < l)
    (p q : ℤ) (u v : CutRing) (huv : ordinary u ≤ ordinary v)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k) (i : Fin l) :
    SmallControlled B.c (B.rectangleCopy hlarge g
      (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i))
      (B.axisSector hlarge n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q i)) := by
  simpa only [axisCellRectangle,otherAxis_ne,ite_false,windowCell] using
    B.rectangleCopy_axes_control hlarge g
      (axisCellRectangle d k l hk hl hlpos p q u v huv hu hv i) (otherAxis d)

theorem axisCellRectangle_distinct_commute (hlarge : 20 ≤ m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k k' l : ℕ) (hk : k ≤ n) (hk' : k' ≤ n) (hl : l ≤ n) (hlpos : 201 ≤ l)
    (p p' q : ℤ) (u v u' v' : CutRing)
    (huv : ordinary u ≤ ordinary v) (huv' : ordinary u' ≤ ordinary v')
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
    (hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k')
    (i j : Fin l) (hij : i ≠ j) (s t : TrackStar (Fin (m+1))) :
    Commute (B.rectangleCopy (by omega) g (axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i) s)
      (B.rectangleCopy (by omega) g (axisCellRectangle d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j) t) := by
  let R := axisCellRectangle d k l hk hl (by omega) p q u v huv hu hv i
  let R' := axisCellRectangle d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j
  refine (small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using hlarge) (B.rectangleCopy (by omega) g R) (B.rectangleCopy (by omega) g R')
    (B.axisSector (by omega) n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q i))
    (B.axisSector (by omega) n g (otherAxis d) l hl q (windowCell a (otherAxis d) l q j))
    (B.rectangleCopy_supported (by omega) g R) (B.rectangleCopy_supported (by omega) g R')
    (B.axisSector_supported (by omega) n g (otherAxis d) l hl q _
      (windowCell_axis_resolved _ _ (by omega) _ _))
    (B.axisCellRectangle_grid_control (by omega) n g d k l hk hl (by omega) p q u v huv hu hv i)
    (B.axisCellRectangle_grid_control (by omega) n g d k' l hk' hl (by omega) p' q u' v' huv' hu' hv' j) ?_) s t
  intro x y
  exact B.fullGeometricSector_commute (by omega) (axisWindowPrimitives (otherAxis d) l q) _ _ _
    (windowCell_axis_resolved _ _ (by omega) _ _)
    (windowCell_pairwise_disjoint (otherAxis d) l hlpos q hij) x y

end InitialCoverSystem
end AxisCellSplitting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AxisSplitting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section AxisSplitting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_split_commute (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (s t : TrackStar (Fin (m+1))) :
    Commute (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) s)
      (B.axisSector hlarge n g d k hk p (coordinateInterval a d v w) t) :=
  B.fullGeometricSector_commute hlarge _ _ _ _ (axisInterval_resolved d k p u v hu hv)
    (coordinateInterval_disjoint d u v v w huv le_rfl hvw hlen) s t

end InitialCoverSystem
end AxisSplitting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SeparatedAxisSectors

theorem transverse_window_mesh (n : ℕ) (hn : 1005 ≤ n) (q : ℤ) (i : Fin (n/4)) :
    ordinary (windowCut (n/4) q i.succ)-ordinary (windowCut (n/4) q i.castSucc) ≤ 1000/(n:ℝ) := by
  apply (windowCut_mesh (n/4) q i).trans
  have hp : (0:ℝ) < ((n/4:ℕ):ℝ) := by exact_mod_cast (show 0 < n/4 by omega)
  have hnp : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : (n:ℝ) ≤ 5*((n/4:ℕ):ℝ) := by exact_mod_cast (show n ≤ 5*(n/4) by omega)
  apply (div_le_div_iff₀ hp hnp).mpr
  linarith

namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem separated_axis_sectors_commute (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (k k' : ℕ) (hk : k ≤ n*9/10) (hk' : k' ≤ n*9/10)
      (p p' : ℤ) (u v u' v' : CutRing)
      (_huv : ordinary u ≤ ordinary v) (_hgap : ordinary v < ordinary u')
      (_huv' : ordinary u' ≤ ordinary v')
      (_hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
      (_hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
      (_hu' : p' ≤ endpointLabel u' ∧ endpointLabel u' < p'+k')
      (_hv' : p' ≤ endpointLabel v' ∧ endpointLabel v' < p'+k'),
      ordinary v'-ordinary u ≤ C/(n:ℝ) →
      |(endpointLabel (u'-v):ℝ)| ≤ 6*(n:ℝ)/5 →
      ∀ x y, Commute
        (B.axisSector (by omega) n g d k (by omega) p (coordinateInterval a d u v) x)
        (B.axisSector (by omega) n g d k' (by omega) p' (coordinateInterval a d u' v') y) := by
  obtain ⟨N₀,hN₀,hcomm⟩ := separated_old_rectangles_commute
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort (by linarith : 0 ≤ C) hSlope hconj
  refine ⟨max 1005 N₀,by omega,?_⟩
  intro M B h n hn g d k k' hk hk' p p' u v u' v' huv hgap huv' hu hv hu' hv' hwidth hlabels x y
  have hnpos : 1005 ≤ n := by omega
  let f (i : Fin (n/4)) := B.rectangleCopy (by omega) g
    (axisCellRectangle d k (n/4) (by omega) (by omega) (by omega) p 0 u v huv hu hv i)
  let f' (i : Fin (n/4)) := B.rectangleCopy (by omega) g
    (axisCellRectangle d k' (n/4) (by omega) (by omega) (by omega) p' 0 u' v' huv' hu' hv' i)
  have hc (i j : Fin (n/4)) (x y : TrackStar (Fin (m+1))) : Commute (f i x) (f' j y) := by
    by_cases hij : i=j
    · subst j
      let P := axisCellStripPair d k k' (n/4) (by omega) (by omega) (by omega) (by omega)
        p p' 0 u v u' v' huv hgap huv' hu hv hu' hv' hk hk' le_rfl i
      exact hcomm M B h n (by omega) g d P hwidth
        ((transverse_window_mesh n hnpos 0 i).trans
          (div_le_div_of_nonneg_right hC (by positivity))) hlabels x y
    · exact B.axisCellRectangle_distinct_commute hlarge n g d k k' (n/4)
        (by omega) (by omega) (by omega) (by omega) p p' 0 u v u' v' huv huv' hu hv hu' hv' i j hij x y
  exact commute_of_range_iSup f f' hc
    (B.axisSector_range_cells (by omega) n g d k (n/4) (by omega) (by omega) (by omega)
      p 0 u v huv hu hv ⟨x,rfl⟩)
    (B.axisSector_range_cells (by omega) n g d k' (n/4) (by omega) (by omega) (by omega)
      p' 0 u' v' huv' hu' hv' ⟨y,rfl⟩)

end InitialCoverSystem
end SeparatedAxisSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisCutSequences
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem index_mono : Monotone D.index := by
  intro i j hij
  exact min_le_min_right K hij

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

theorem prefix_suffix_self_commute (hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1)
    (i : ℕ) (s t : TrackStar (Fin (m+1))) :
    Commute (D.prefixCopy B hlarge g d i s) (D.suffix B hlarge g d i t) :=
  B.axisSector_split_commute hlarge n g d _ _ _ _ _ _
    (D.ordered _).1 (D.ordered _).2 hlen (D.lower_label _) (D.cut_label _) s t

end AxisCutSequence
end AxisCutSequences

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AxisCutCommutation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section AxisCutCommutation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axis_cut_sequence_commutations_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (K : ℕ) (D : AxisCutSequence n K),
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) ≤ C/(n:ℝ) →
      (∀ i j, |(endpointLabel (D.cut j-D.cut i):ℝ)| ≤ 6*(n:ℝ)/5) →
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 ∧
      ∀ i j : ℕ, i ≤ j → ∀ x y,
        Commute (D.prefixCopy B (by omega) g d i x) (D.suffix B (by omega) g d j y) := by
  obtain ⟨N₀,hN₀,hcomm⟩ := separated_axis_sectors_commute
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt C
  refine ⟨max N₀ N₁,by omega,?_⟩
  intro M B h n hn g d K D hwidth hlabels
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hCn : C < (n:ℝ) := hN₁.trans_le (by exact_mod_cast (show N₁ ≤ n by omega))
  have hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 :=
    hwidth.trans_lt ((div_lt_one hnp).mpr hCn)
  refine ⟨hlen,?_⟩
  intro i j hij x y
  have hle := D.index_mono hij
  rcases eq_or_lt_of_le hle with he | hlt
  · have hp : D.prefixCopy B (by omega) g d i = D.prefixCopy B (by omega) g d j := by
      simp only [AxisCutSequence.prefixCopy,he]
    rw [hp]
    exact D.prefix_suffix_self_commute B (by omega) g d hlen j x y
  · exact hcomm M B h n (by omega) g d _ _ (D.length_le _) (D.length_le _)
      _ _ _ _ _ _ (D.ordered _).1 (D.strictMono hlt) (D.ordered _).2
      (D.lower_label _) (D.cut_label _) (D.cut_label _) (D.upper_label _)
      hwidth (hlabels _ _) x y

end InitialCoverSystem
end AxisCutCommutation

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations_oai := @OAI.SimpleAmenable.InitialCoverSystem.axis_cut_sequence_commutations_oai
