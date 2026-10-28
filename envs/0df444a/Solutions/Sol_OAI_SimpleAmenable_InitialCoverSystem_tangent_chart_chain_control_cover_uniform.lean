-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:03:41.789482+00:00
-- url     : https://prove2.me/submissions/36272db3-f5df-4e55-87cf-c39f9db432d3

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_old_rectangle_bridge_control_cover_uniform

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorOffsetCoherence
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
section SectorOffsetCoherence

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*}

theorem primitiveFamily_congr_offsets (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1)) :
    B.primitiveFamily I b hb P = B.primitiveFamily I b hb Q := by
  funext i
  cases i with
  | none => rfl
  | some i =>
    change B.primitiveCopy I b hb (P i) = B.primitiveCopy I b hb (Q i)
    have he : P i = ((Q i).1,(P i).2) := Prod.ext (hj i) rfl
    rw [he]
    exact B.primitiveCopy_translate_eq I b hb (Q i).1 (P i).2 (Q i).2
      (by simpa only [hj i] using hp i)

variable [Finite ι] [Finite κ]

theorem geometricSector_congr_offsets (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : B.PrimitiveFamilyLaw I b hb P) (g : B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.geometricSector I b hb P h V = B.geometricSector I b hb Q g V := by
  have he := B.primitiveFamily_congr_offsets I b hb P Q hj hp
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    intro x y hxy
    apply hV x y
    intro i
    change x ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val ↔
      y ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val
    rw [hp i]
    exact hxy i
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb Q)).range g
  · rintro x ⟨s,rfl⟩
    rw [← he]
    exact B.geometricSector_mem I b hb P h V s
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb Q g V s
  · rw [B.geometricSector_projection I b hb P h V hV,
      B.geometricSector_projection I b hb Q g V hV']

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_congr_offsets (hlarge : 15 < m+1)
    (P Q : ι → Fin 5 × (CutRing × CutRing))
    (hj : ∀ i, (P i).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P i).2 (initialTest a r (P i).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.fullGeometricSector hlarge P h V = B.fullGeometricSector hlarge Q g V := by
  have hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    intro x y hxy
    apply hV x y
    intro i
    change x ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val ↔
      y ∈ (spatialTranslate (P i).2 (initialTest a r (P i).1)).val
    rw [hp i]
    exact hxy i
  apply universal_five_alphabet_hom_ext (by simp; omega)
  intro I
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  rw [B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
      (h _ (by rw [I.property.2]; omega) b hb) V hV,
    B.fullGeometricSector_inclusion hlarge Q g I.val (by rw [I.property.2]) b hb
      (g _ (by rw [I.property.2]; omega) b hb) V hV']
  exact B.geometricSector_congr_offsets I.val b hb P Q hj hp _ _ V hV

end InitialCoverSystem
end SectorOffsetCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoordinateFamilyCompare
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
section CoordinateFamilyCompare

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_compare (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (v : κ → ι)
    (hj : ∀ i, (P (v i)).1 = (Q i).1)
    (hp : ∀ i, spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1) =
      spatialTranslate (Q i).2 (initialTest a r (Q i).1))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (g : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge Q g V = B.fullGeometricSector hlarge P h V := by
  let R := P ∘ v
  have hR : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb R :=
    fun I hI b hb => PrimitiveFamilyLaw.reindex B I b hb P (h I hI b hb) v
  have hVR : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) R i).val) V.val := by
    intro x y he
    apply hV x y
    intro i
    have hh := he i
    change x ∈ (spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1)).val ↔
      y ∈ (spatialTranslate (P (v i)).2 (initialTest a r (P (v i)).1)).val at hh
    rw [hp i] at hh
    exact hh
  rw [← B.fullGeometricSector_congr_offsets hlarge R Q hj hp hR g V hVR]
  exact B.fullGeometricSector_subfamily hlarge P R v rfl h hR V hVR

omit [Finite κ] in
theorem coordinateFamilySector_eq_window (hlarge : 15 < m+1)
    (n : ℕ) (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (j : ι → Fin 2) (u : ι → CutRing × CutRing)
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i = 0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i = 0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ))
    (g : ∀ I, I.card ≤ 15 → ∀ b hb,
      B.PrimitiveFamilyLaw I b hb (fun i => (coordinateTestIndex (j i),u i)))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (spatialTranslate (u i) (coordinatePrimitive a (j i))).val) V.val) :
    B.fullGeometricSector hlarge (fun i => (coordinateTestIndex (j i),u i)) g V =
      B.windowSector hlarge n h q V := by
  obtain ⟨v,hj,hp⟩ := coordinateFamily_window_reindex (a := a) (r := r) n q j u hs he
  apply B.fullGeometricSector_compare hlarge _ _ v hj hp _ g V
  simpa only [primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV

end InitialCoverSystem
end CoordinateFamilyCompare

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ChartControlChain
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
section ChartControlChain

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem small_control_action_chain (c : alternatingGroup α →* H)
    (f : TrackStar α →* H) (g : ℕ → TrackStar α →* H) (n : ℕ)
    (hstart : SmallControlled c f (g 0))
    (hstep : ∀ k, k < n → ∀ (I : ControlAlphabet α) s, ∀ x ∈ f.range,
      g k (universalMap (subtypeAlternatingHom I.val) s)*x*
          (g k (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        g (k+1) (universalMap (subtypeAlternatingHom I.val) s)*x*
          (g (k+1) (universalMap (subtypeAlternatingHom I.val) s))⁻¹) :
    SmallControlled c f (g n) := by
  have h (k : ℕ) (hk : k ≤ n) : SmallControlled c f (g k) := by
    induction k with
    | zero => exact hstart
    | succ k ih =>
      intro I s x hx
      dsimp only [MonoidHom.comp_apply]
      rw [← hstep k (by omega) I s x hx]
      exact ih (by omega) I s x hx
  exact h n le_rfl

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem chartCoordinateSector_eq_window (hlarge : 15 < m+1)
    (n : ℕ) (h : B.CoordinateWindowLaw n) (q : Fin 2 → ℤ)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hP : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (v : κ → ι) (j : κ → Fin 2) (u : κ → CutRing × CutRing)
    (hv : ∀ i, P (v i) = (coordinateTestIndex (j i),u i))
    (hs : ∀ i, q (j i) ≤ endpointLabel (if j i=0 then (u i).1 else (u i).2))
    (he : ∀ i, endpointLabel (if j i=0 then (u i).1 else (u i).2) < q (j i)+(n-1:ℕ))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (spatialTranslate (u i) (coordinatePrimitive a (j i))).val) V.val) :
    B.fullGeometricSector hlarge P hP V = B.windowSector hlarge n h q V := by
  let Q := fun i => (coordinateTestIndex (j i),u i)
  have heq : P ∘ v = Q := funext hv
  have hQ : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q := by
    intro I hI b hb
    rw [← heq]
    exact PrimitiveFamilyLaw.reindex B I b hb P (hP I hI b hb) v
  have hVQ : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val := by
    simpa only [Q,primitiveTests,primitiveFamilyTests,initialTest_coordinate] using hV
  rw [← B.fullGeometricSector_subfamily hlarge P Q v heq hP hQ V hVQ]
  exact B.coordinateFamilySector_eq_window hlarge n h q j u hs he hQ V hV

end InitialCoverSystem
end ChartControlChain

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

theorem clippedSlope_agree_on_rectangle {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (u v : CutRing × CutRing) (l h : Fin 2 → CutRing)
    (hlh : ∀ k, ordinary (l k) ≤ ordinary (h k))
    (hlen : ∀ k, ordinary (h k)-ordinary (l k) < 1)
    (hu : ∀ k, -ordinary r < ordinary (l k)-ordinary (if k=0 then u.1 else u.2) ∧
      ordinary (h k)-ordinary (if k=0 then u.1 else u.2) < ordinary r)
    (hv : ∀ k, -ordinary r < ordinary (l k)-ordinary (if k=0 then v.1 else v.2) ∧
      ordinary (h k)-ordinary (if k=0 then v.1 else v.2) < ordinary r)
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
  · obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift l h hlh hlen p hp
    have hbox (w : CutRing × CutRing)
        (hw : ∀ k : Fin 2, -ordinary r < ordinary (l k)-ordinary (if k=0 then w.1 else w.2) ∧
          ordinary (h k)-ordinary (if k=0 then w.1 else w.2) < ordinary r) :
        (-ordinary r < t.1-ordinary w.1 ∧ t.1-ordinary w.1 < ordinary r) ∧
          (-ordinary r < t.2-ordinary w.2 ∧ t.2-ordinary w.2 < ordinary r) := by
      have hw0 := hw 0
      have hw1 := hw 1
      simp only [ite_true,Fin.isValue,show (1:Fin 2) ≠ 0 by decide,ite_false] at hw0 hw1
      constructor <;> constructor <;> linarith
    rw [translated_clippedSlope_lift r j hr u p t ht (hbox u hu),
      translated_clippedSlope_lift r j hr v p t ht (hbox v hv),hline]
  · simp only [hp,and_false]

end SpatialChartGeometry

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

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentSign_step_action (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ j, -ordinary r < ordinary (l j)-ordinary
          (if j=0 then (tangentOffset a d (signedShortSteps u e)).1
           else (tangentOffset a d (signedShortSteps u e)).2) ∧
        ordinary (v j)-ordinary
          (if j=0 then (tangentOffset a d (signedShortSteps u e)).1
           else (tangentOffset a d (signedShortSteps u e)).2) < ordinary r)
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
  have he := clippedSlope_agree_on_rectangle (a := a) r (slopeDirection d) hr
    (0 : CutRing × CutRing) (tangentOffset a d (signedShortSteps u e)) l v hlv hlen
    (by simpa using hbox) hbox' (by simp only [integralCutForm_zero,integralCutForm_tangentOffset])
  have he' := congrArg (spatialTranslate z) he
  simpa only [spatialTranslate_inter,← spatialTranslate_add,add_zero] using he'

end InitialCoverSystem
end TangentChartAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LabelShiftedCharts
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
section LabelShiftedCharts

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentChartSector_eq_window (hlarge : 15 < m+1)
    (k : ℕ) (p : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k p u)
    (n : ℕ) (hn : k ≤ n) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, p j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < p j+k)
    (hv : ∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+k) :
    B.fullGeometricSector hlarge
      (translatedTemplate (tangentChartTemplate a k p d (signedShortSteps u e)) z) (h d e z)
      (spatialTranslate z (coordinateRectangle a l v)) =
    B.windowSector hlarge n g (fun j => pointLabel z j+p j)
      (spatialTranslate z (coordinateRectangle a l v)) := by
  apply B.chartCoordinateSector_eq_window hlarge n g (fun j => pointLabel z j+p j)
    _ (h d e z) Sum.inr Prod.fst (fun i => z+(coordinateWindowPrimitives k p i).2)
  · intro i
    rfl
  · intro i
    change pointLabel z i.1+p i.1 ≤ pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    omega
  · intro i
    change pointLabel (z+(coordinateWindowPrimitives k p i).2) i.1 <
      pointLabel z i.1+p i.1+(n-1:ℕ)
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hi := i.2.isLt
    omega
  · intro x y he
    apply (translatedTemplate_resolved (a := a) (r := r) (coordinateWindowPrimitives k p)
      (coordinateRectangle a l v) (fun x y he => and_congr
        (coordinateLabelWindow_resolved k p 0 (l 0) (v 0) (hl 0) (hv 0) x y he)
        (coordinateLabelWindow_resolved k p 1 (l 1) (v 1) (hl 1) (hv 1) x y he)) z) x y
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,coordinateWindowPrimitives,
      initialTest_coordinate] using he

end InitialCoverSystem
end LabelShiftedCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoverUniformBridges
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
section CoverUniformBridges
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem old_rectangle_bridge_to_chart_cover_uniform (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
      ∀ L V : Fin 2 → CutRing,
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
      ∀ (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing),
      (∀ j, ((pointLabel z j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      (∀ j, ordinary (l j)+ordinary (pointCoordinate z j) ≤ ordinary (L j)-δ) →
      (∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate z j)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.fullGeometricSector (by omega)
        (translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u e)) z)
        (h d e z) (spatialTranslate z (coordinateRectangle a l v))) := by
  obtain ⟨N,hN,hbridge⟩ := old_rectangle_bridge_control_cover_uniform (a := a) (r := r) (hm := hm) hlarge hK hδ
  refine ⟨max N (8*k),le_trans hN (le_max_left _ _),?_⟩
  intro M B h n hn g s hs p L V hLV hL hV d e z hpq hlo hup f hf hc
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hkn : k ≤ n/8 := (Nat.le_div_iff_mul_le (by omega : 0 < 8)).mpr (by omega)
  rw [B.tangentChartSector_eq_window (by omega) k q u h n (by omega) g d e z l v hl hv,
    spatialTranslate_coordinateRectangle]
  apply hbridge M B n hnN g s hs p (fun j => pointLabel z j+q j) hpq L V
    (fun j => l j+pointCoordinate z j) (fun j => v j+pointCoordinate z j) hLV
  · intro j
    simpa only [map_add] using hlo j
  · intro j
    simpa only [map_add] using hup j
  · intro j
    simpa only [map_add,add_sub_add_right_eq_sub] using hlen j
  · exact hL
  · exact hV
  · intro j
    simp only [endpointLabel_add,pointLabel]
    have hh := hl j
    omega
  · intro j
    simp only [endpointLabel_add,pointLabel]
    have hh := hv j
    omega
  · exact hf
  · exact hc

theorem tangent_chart_chain_control_cover_uniform_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hlv : ∀ j, ordinary (l j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1)
    (hbox : ∀ j, -ordinary r < ordinary (l j) ∧ ordinary (v j) < ordinary r)
    (hbox' : ∀ (d : Fin 2) (e : Fin 5) (j : Fin 2),
      -ordinary r < ordinary (l j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary (v j)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M) (h : B.TangentChartLaws k q u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p : Fin 2 → ℤ),
      ∀ L V : Fin 2 → CutRing,
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+s j) →
      ∀ (d : Fin 2) (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
      (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) →
      (∀ i, i < T → ∀ j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      (∀ i, i < T → ∀ j, ordinary (l j)+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-δ) →
      (∀ i, i < T → ∀ j, ordinary (V j)+δ ≤ ordinary (v j)+ordinary (pointCoordinate (z i) j)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (s j) (hs j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z 0) true) →
      SmallControlled B.c f (B.tangentSign (by omega) k q u h d (z T) true) := by
  obtain ⟨N,hN,hbridge⟩ := old_rectangle_bridge_to_chart_cover_uniform (m := m) (r := r) (hm := hm) hlarge hK hδ k q u l v hl hv hlen
  refine ⟨N,hN,?_⟩
  intro M B h n hn g s hs p L V hLV hL hV d T z e hz hpq hlo hup f hf hc hstart
  apply small_control_action_chain B.c f
    (fun i => B.tangentSign (by omega) k q u h d (z i) true) T hstart
  intro i hi I t x hx
  rw [hz i hi]
  exact B.tangentSign_step_action hlarge hr k q u h d (e i) (z i) l v hl hv hlv hlen hbox
    (hbox' d (e i)) f hf
    (hbridge M B h n hn g s hs p L V hLV hL hV d (e i) (z i) (hpq i hi) (hlo i hi) (hup i hi) f hf hc)
    I t x hx

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform_oai := @OAI.SimpleAmenable.InitialCoverSystem.tangent_chart_chain_control_cover_uniform_oai
