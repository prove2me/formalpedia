-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:01:11.854411+00:00
-- url     : https://prove2.me/submissions/9e59c67e-341d-4f8b-ae29-06a7c2a18c0c

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_ConcurrentGeometry_InwardChart_refined_cells_locally_decided
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_uniform_clipped_model_action_neighborhood

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

theorem finite_grid_endpoint_decision {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (i : Fin N) (c : CutRing) (hc : cutFraction c ∈ Set.range e) (k : ℤ)
    (j : Fin 2) (x y : GenericSquare a)
    (hx : ordinary (e i.castSucc) ≤ coordinate j x ∧ coordinate j x<ordinary (e i.succ))
    (hy : ordinary (e i.castSucc) ≤ coordinate j y ∧ coordinate j y<ordinary (e i.succ)) :
    coordinate j x+(k:ℝ)<ordinary c ↔ coordinate j y+(k:ℝ)<ordinary c := by
  rcases finite_grid_endpoint_sides e he hzero hlast i c hc k with hh | hh
  · have h₁ : ¬coordinate j x+(k:ℝ)<ordinary c := by linarith [hx.1]
    have h₂ : ¬coordinate j y+(k:ℝ)<ordinary c := by linarith [hy.1]
    exact iff_of_false h₁ h₂
  · exact iff_of_true (by linarith [hx.2]) (by linarith [hy.2])

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

end ClosedRefinementContainment

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalClippedBoxFormula
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

omit [Finite ι] in

theorem refined_coordinate_phase {κ : Type*} [Finite κ]
    {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (d : κ → Fin 2) (v : κ → CutRing) (f : κ → ι)
    (hf : ∀ k, j (f k)=axisDirection (d k) ∧ c (f k)=v k)
    (hv : ∀ k, cutFraction (v k) ∈ Set.range e)
    (hlocal : ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧ ∀ i,
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val) :
    ∃ σ : κ → Bool, refinedGridRectangle a N e cell ≤
      C.coordinateGate T.vertex T.offset z d v σ := by
  classical
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh cell
  let σ := polygonAssignment (fun k => C.localDecision T.vertex T.offset z (axisDirection (d k)) (v k)) x
  refine ⟨σ,fun y hy => ⟨(hlocal y hy).1,?_⟩⟩
  funext k
  apply decide_eq_decide.mpr
  have hxy := finite_grid_endpoint_decision e he hzero hlast (cell (d k)) (v k) (hv k) 0 (d k) y x
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell y).mp hy (d k))
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx (d k))
  have hy' := (hlocal y hy).2 (f k)
  have hx' := (hlocal x hx).2 (f k)
  rw [(hf k).1,(hf k).2] at hy' hx'
  refine Iff.trans hy' (Iff.trans ?_ hx'.symm)
  simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,cutForm_axis,coordinate,realCoordinate,
    Int.cast_zero,add_zero] using hxy

omit [Finite ι] in

theorem refined_interior_phase_bounds {N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (v : CutRing × CutRing)
    (lo hi : Fin 2 → ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate v d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate v d+r)
    (hlor : ∀ d, cutFraction (pointCoordinate v d-r) ∈ Set.range e)
    (hhir : ∀ d, cutFraction (pointCoordinate v d+r) ∈ Set.range e)
    (σ : Fin 2 × Bool → Bool) (hσ : ∀ d, σ (d,false)=false ∧ σ (d,true)=true)
    (hgate : refinedGridRectangle a N e cell ≤ C.coordinateGate T.vertex T.offset z Prod.fst
      (fun k => if k.2 then pointCoordinate v k.1+r else pointCoordinate v k.1-r) σ)
    (hlocal : ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val → ∀ i,
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val) :
    ∀ d, -ordinary r≤ordinary (e (cell d).castSucc)-ordinary (pointCoordinate v d) ∧
      ordinary (e (cell d).succ)-ordinary (pointCoordinate v d)≤ordinary r := by
  obtain ⟨x,hx⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh cell
  have hassign := (hgate hx).2
  intro d
  have hl := congrFun hassign (d,false)
  have hh := congrFun hassign (d,true)
  have hlocalL := hlocal x hx (lo d)
  have hlocalH := hlocal x hx (hi d)
  rw [(hlo d).1,(hlo d).2] at hlocalL
  rw [(hhi d).1,(hhi d).2] at hlocalH
  have hl' : ¬ x ∈ (C.localDecision T.vertex T.offset z (axisDirection d) (pointCoordinate v d-r)).val := by
    simpa only [polygonAssignment,Bool.false_eq_true,↓reduceIte,(hσ d).1,decide_eq_false_iff_not] using hl
  have hh' : x ∈ (C.localDecision T.vertex T.offset z (axisDirection d) (pointCoordinate v d+r)).val := by
    simpa only [polygonAssignment,↓reduceIte,(hσ d).2,decide_eq_true_eq] using hh
  simp only [cutPolygon,halfPlane,Set.mem_ofPred_eq,cutForm_axis] at hlocalL hlocalH
  have hb : ordinary (pointCoordinate v d-r) ≤ coordinate d x ∧
      coordinate d x < ordinary (pointCoordinate v d+r) := by
    exact ⟨le_of_not_gt (fun h => hl' (hlocalL.mpr h)),hlocalH.mp hh'⟩
  have hf := finite_grid_interval_lift e he hzero hlast (cell d)
    (pointCoordinate v d-r) (pointCoordinate v d+r) (hlor d) (hhir d) (coordinate d x)
    ((refinedGridRectangle_mem e he hzero hlast hmesh cell x).mp hx d) 0
    (by simpa only [Int.cast_zero,add_zero] using hb)
  simp only [Int.cast_zero,add_zero,map_sub,map_add] at hf
  constructor <;> linarith [hf.1,hf.2]

end ConcurrentGeometry.InwardChart

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RefinedLocalDecisions
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
section RefinedLocalDecisions

theorem refinedGridRectangle_point_near {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (z : ℝ × ℝ) (δ : ℝ)
    (hnear : ∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ)
    (p : GenericSquare a) (hp : p ∈ (refinedGridRectangle a N e cell).val) : dist p.val z<δ := by
  have hb := (refinedGridRectangle_mem e he hzero hlast hmesh cell p).mp hp
  have hd (k : Fin 2) : |realCoordinate p.val k-realCoordinate z k|<δ := by
    have hl := (abs_lt.mp (hnear k).1).1
    have hr := (abs_lt.mp (hnear k).2).2
    have hk := hb k
    change ordinary (e (cell k).castSucc) ≤ realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary (e (cell k).succ) at hk
    rw [abs_lt]
    constructor <;> linarith [hk.1,hk.2]
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
  exact ⟨hd 0,hd 1⟩

end RefinedLocalDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_RefinedClippedModels
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

theorem refined_clipped_model_action_neighborhood_oai {ι : Type*} [Finite ι]
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (G : ClippedGerm a r (slopeDirection d) u z) (hbox : G.BoxValid)
    {j : ι → Fin 4} {c : ι → CutRing} (T : A.geometry.InwardChart j c z)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (slope : ι)
    (hlo : ∀ k, j (lo k)=axisDirection k ∧ c (lo k)=pointCoordinate G.offset k-r)
    (hhi : ∀ k, j (hi k)=axisDirection k ∧ c (hi k)=pointCoordinate G.offset k+r)
    (hs : j slope=slopeDirection d ∧ c slope=integralCutForm a (slopeDirection d) G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))).val)
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    : ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    (∀ k, cutFraction (pointCoordinate G.offset k-r) ∈ Set.range e) →
    (∀ k, cutFraction (pointCoordinate G.offset k+r) ∈ Set.range e) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ (n : ℕ) (q : Fin 2 → ℤ),
    ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (refinedGridRectangle a N e cell).val →
    ∀ initial : Fin 2 → Fin A.geometry.mesh,
    refinedGridRectangle a N e cell ≤ spatialTranslate G.offset
      (windowRectangle a A.geometry.mesh (symmetricWindowStart r) initial) →
    ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
    B.AlignedSmallSupported f →
    SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (refinedGridRectangle a N e cell)) →
    ∀ (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)),
    ∀ x ∈ f.range,
    A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s)*x*
      (A.primitiveStar (by omega) (slopeTestIndex d,u) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
      (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
        (universalMap (subtypeAlternatingHom I.val) s)*x*
      (B.fullGeometricSector (by omega) (A.concurrentPrimitives T.vertex T.offset) (A.concurrentLaw T.vertex T.offset)
        (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r (slopeDirection d))) ())
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨δ₀,hδ₀,hdecisions⟩ := T.refined_cells_locally_decided hr
  obtain ⟨δ₁,hδ₁,hact⟩ := A.uniform_clipped_model_action_neighborhood hlarge hr d u z G hbox T hz₁ hz₂
    lo hi slope hlo hhi hs hR hmesh
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro N e he hzero hlast hmesh' hlor hhir cell hnear n q hW initial hinitial f hf hc I s x hx
  have hnear₀ k := And.intro ((hnear k).1.trans_le (min_le_left δ₀ δ₁))
    ((hnear k).2.trans_le (min_le_left δ₀ δ₁))
  have hnear₁ k := And.intro ((hnear k).1.trans_le (min_le_right δ₀ δ₁))
    ((hnear k).2.trans_le (min_le_right δ₀ δ₁))
  have hlocal := hdecisions N e he hzero hlast hmesh' cell hnear₀
  let idx (k : Fin 2 × Bool) : ι := if k.2 then hi k.1 else lo k.1
  have hidx (k : Fin 2 × Bool) : j (idx k)=axisDirection k.1 ∧ c (idx k)=G.axialCut k := by
    obtain ⟨k,b⟩ := k
    cases b
    · exact hlo k
    · exact hhi k
  have hends (k : Fin 2 × Bool) : cutFraction (G.axialCut k) ∈ Set.range e := by
    obtain ⟨k,b⟩ := k
    cases b
    · exact hlor k
    · exact hhir k
  obtain ⟨σ,hgate⟩ := T.refined_coordinate_phase e he hzero hlast hmesh' cell Prod.fst G.axialCut idx hidx hends hlocal
  obtain ⟨p,hp⟩ := refinedGridRectangle_nonempty e he hzero hlast hmesh' cell
  apply hact σ (fun k => e (cell k).castSucc) (fun k => e (cell k).succ)
    (fun k => (he (Fin.castSucc_lt_succ (i := cell k))).le) ?_ hnear₁ n q hW hgate initial hinitial p hp
    (refinedGridRectangle_point_near e he hzero hlast hmesh' cell z δ₁ hnear₁ p hp)
    ((refinedGridRectangle_mem e he hzero hlast hmesh' cell p).mp hp) f hf hc I s x hx
  intro hσ
  exact T.refined_interior_phase_bounds e he hzero hlast hmesh' cell G.offset lo hi hlo hhi hlor hhir σ hσ
    hgate (fun p hp => (hlocal p hp).2)

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.refined_clipped_model_action_neighborhood_oai.{u_1}
