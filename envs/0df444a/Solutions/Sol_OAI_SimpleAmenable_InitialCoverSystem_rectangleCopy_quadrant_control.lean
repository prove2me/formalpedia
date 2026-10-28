-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:45:40.362424+00:00
-- url     : https://prove2.me/submissions/75f98d0e-8cb7-4c4c-a308-535bcaf26544

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_control_trans

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

theorem same_conj_iff (u v k : H) :
    u*k*u⁻¹ = v*k*v⁻¹ ↔ Commute (u⁻¹*v) k := by
  constructor
  · intro h
    apply commutatorElement_eq_one_iff_commute.mp
    rw [commutatorElement_def]
    calc
      _ = u⁻¹*(v*k*v⁻¹)*u*k⁻¹ := by group
      _ = u⁻¹*(u*k*u⁻¹)*u*k⁻¹ := by rw [← h]
      _ = 1 := by group
  · intro h
    have hc := h.eq
    calc
      u*k*u⁻¹ = u*(k*(u⁻¹*v))*v⁻¹ := by group
      _ = u*((u⁻¹*v)*k)*v⁻¹ := by rw [hc]
      _ = v*k*v⁻¹ := by group

private theorem commutator_four (b c d e : H)
    (hcb : Commute c b) (hce : Commute c e) (hdb : Commute d b)
    (hcd : Commute c d) (hbe : Commute b e) :
    ⁅c*d,b*e⁆ = ⁅d,e⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (hcb.mul_right hce).commutator_eq,mul_one,
    commutatorElement_mul_right_eq_mul_conj,hdb.commutator_eq,one_mul]
  have hb : Commute b ⁅d,e⁆ := by
    rw [commutatorElement_def]
    exact ((hdb.symm.mul_right hbe).mul_right hdb.symm.inv_right).mul_right hbe.inv_right
  have hc : Commute c ⁅d,e⁆ := by
    rw [commutatorElement_def]
    exact ((hcd.mul_right hce).mul_right hcd.inv_right).mul_right hce.inv_right
  calc
    _ = c* ⁅d,e⁆ *c⁻¹ := by rw [hb.eq]; group
    _ = ⁅d,e⁆ := by rw [hc.eq]; group

theorem four_factor_in_subgroup [Group.IsPerfect E]
    (b c d : E →* H) (C : Subgroup H)
    (hbc : ∀ s t, Commute (b s) (c t))
    (hbd : ∀ s t, Commute (b s) (d t))
    (hcd : ∀ s t, Commute (c s) (d t))
    (hJ : ∀ s, c s*d s ∈ C) (hK : ∀ s, b s*d s ∈ C) :
    d.range ≤ C := by
  have hh : ⁅d.range,d.range⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩
    rw [← commutator_four (b t) (c s) (d s) (d t)
      (hbc t s).symm (hcd s t) (hbd t s).symm (hcd s s) (hbd t t)]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hJ s) (hK t)) (C.inv_mem (hJ s)))
      (C.inv_mem (hK t))
  have he : (commutator E).map d = d.range := by
    rw [Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
  rw [← he,map_commutator_eq]
  exact hh

theorem intersection_control [Group.IsPerfect E]
    (a b c d f : E →* H) (P : Subgroup H)
    (hbc : ∀ s t, Commute (b s) (c t))
    (hbd : ∀ s t, Commute (b s) (d t))
    (hcd : ∀ s t, Commute (c s) (d t))
    (hf : ∀ s, f s = a s*b s*c s*d s)
    (hJ : SameActionOn (fun s => a s*b s) f P)
    (hK : SameActionOn (fun s => a s*c s) f P) :
    SameActionOn a f P := by
  let C := Subgroup.centralizer (P : Set H)
  have hJ' (s : E) : c s*d s ∈ C := by
    intro k hk
    have he := (same_conj_iff _ _ _).mp (hJ s k hk)
    rw [hf] at he
    have hu : (a s*b s)⁻¹*(a s*b s*c s*d s) = c s*d s := by group
    rw [hu] at he
    exact he.eq.symm
  have hK' (s : E) : b s*d s ∈ C := by
    intro k hk
    have he := (same_conj_iff _ _ _).mp (hK s k hk)
    rw [hf] at he
    have hu : (a s*c s)⁻¹*(a s*b s*c s*d s) = b s*d s := by
      calc
        _ = (c s)⁻¹*b s*c s*d s := by group
        _ = (c s)⁻¹*c s*b s*d s := by
          simp only [mul_assoc]
          rw [← mul_assoc (b s) (c s) (d s), (hbc s s).eq, mul_assoc]
        _ = b s*d s := by group
    rw [hu] at he
    exact he.eq.symm
  have hd := four_factor_in_subgroup b c d C hbc hbd hcd hJ' hK'
  have hb (s : E) : b s ∈ C := by
    simpa using C.mul_mem (hK' s) (C.inv_mem (hd ⟨s,rfl⟩))
  have hc (s : E) : c s ∈ C := by
    simpa using C.mul_mem (hJ' s) (C.inv_mem (hd ⟨s,rfl⟩))
  intro s k hk
  apply (same_conj_iff _ _ _).mpr
  rw [hf]
  have hu : (a s)⁻¹*(a s*b s*c s*d s) = b s*c s*d s := by group
  rw [hu]
  exact (C.mul_mem (C.mul_mem (hb s) (hc s))
    (hd ⟨s,rfl⟩) k hk).symm

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowSubfamilies
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

section CircularIntervals

theorem coordinateInterval_mono {a : ℕ} (j : Fin 2) (u v u' v' : CutRing)
    (hu : ordinary u' ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hv : ordinary v ≤ ordinary v') (hlen : ordinary v'-ordinary u' < 1) :
    coordinateInterval a j u v ≤ coordinateInterval a j u' v' := by
  intro p hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff j u v huv (by linarith) p).mp hp
  exact (mem_coordinateBetween_iff j u' v' (by linarith) hlen p).mpr
    ⟨k,hu.trans hk.1,hk.2.trans_le hv⟩

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

end InitialCoverSystem
end FullSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorOffsetCoherence
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

theorem small_control_intersection (f a b d e : TrackStar α →* H)
    (hbd : ∀ s t, Commute (b s) (d t))
    (hbe : ∀ s t, Commute (b s) (e t))
    (hde : ∀ s t, Commute (d s) (e t))
    (hwhole : ∀ s, c (universalProjection (alternatingGroup α) s) = a s*b s*d s*e s)
    (hJ : ∀ I : ControlAlphabet α,
      SameActionOn (fun t => a (universalMap (subtypeAlternatingHom I.val) t)*
        b (universalMap (subtypeAlternatingHom I.val) t))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range)
    (hK : ∀ I : ControlAlphabet α,
      SameActionOn (fun t => a (universalMap (subtypeAlternatingHom I.val) t)*
        d (universalMap (subtypeAlternatingHom I.val) t))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range) :
    SmallControlled c f a := by
  intro I
  exact intersection_control
    (a.comp (universalMap (subtypeAlternatingHom I.val)))
    (b.comp (universalMap (subtypeAlternatingHom I.val)))
    (d.comp (universalMap (subtypeAlternatingHom I.val)))
    (e.comp (universalMap (subtypeAlternatingHom I.val)))
    ((c.comp (universalProjection (alternatingGroup α))).comp
      (universalMap (subtypeAlternatingHom I.val))) f.range
    (fun s t => hbd _ _) (fun s t => hbe _ _) (fun s t => hde _ _)
    (fun s => hwhole _) (hJ I) (hK I)

end SmallControlTransfer

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ChartControlChain
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
section ChartControlChain

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntersectionControl
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
section IntersectionControl
namespace ActualLawfulTable
variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_split (U V : Set Ω) (s : UniversalExtension E) :
    T.sector U s = T.sector (U ∩ V) s*T.sector (U \ V) s := by
  have hd : Disjoint (U ∩ V) (U \ V) := Set.disjoint_left.mpr (by aesop)
  have he : (U ∩ V) ∪ (U \ V) = U := by ext x; simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff]; tauto
  have hh := DFunLike.congr_fun (T.sector_union hd) s
  simpa only [he,commutingProduct_apply] using hh

theorem sector_four_factors (U V : Set Ω) (s : UniversalExtension E) :
    T.sector Set.univ s = T.sector (U ∩ V) s*T.sector (U \ V) s*
      T.sector (V \ U) s*T.sector (U ∪ V)ᶜ s := by
  rw [T.sector_split Set.univ U s]
  rw [Set.univ_inter, ← Set.compl_eq_univ_sdiff]
  rw [T.sector_split U V s,T.sector_split Uᶜ V s]
  have he₁ : Uᶜ ∩ V = V \ U := by ext x; simp only [Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_sdiff]; tauto
  have he₂ : Uᶜ \ V = (U ∪ V)ᶜ := by ext x; simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_sdiff]; tauto
  simp only [he₁,he₂,mul_assoc]

end ActualLawfulTable

variable {α H Q Ω : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]
    {q : H →* Q} {v : (Ω → alternatingGroup α) →* Q}
    (T : ActualLawfulTable q v) (c : alternatingGroup α →* H)

theorem table_small_control_intersection
    (hwhole : T.sector Set.univ = c.comp (universalProjection (alternatingGroup α)))
    (f : TrackStar α →* H) (U V : Set Ω)
    (hU : SmallControlled c f (T.sector U)) (hV : SmallControlled c f (T.sector V)) :
    SmallControlled c f (T.sector (U ∩ V)) := by
  refine small_control_intersection c f (T.sector (U ∩ V)) (T.sector (U \ V))
    (T.sector (V \ U)) (T.sector (U ∪ V)ᶜ) ?_ ?_ ?_ ?_ ?_ ?_
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · exact T.sector_commute (Set.disjoint_left.mpr (by aesop))
  · intro s
    rw [← T.sector_four_factors U V s,hwhole]
    rfl
  · intro I t x hx
    dsimp only
    rw [← T.sector_split U V]
    exact hU I t x hx
  · intro I t x hx
    dsimp only
    have he : V ∩ U = U ∩ V := Set.inter_comm _ _
    have hh := T.sector_split V U (universalMap (subtypeAlternatingHom I.val) t)
    rw [he] at hh
    rw [← hh]
    exact hV I t x hx

variable {a : ℕ} {ι : Type*}

theorem resolvedPolygonMask_inter (U : ι → polygonAlgebra a) (V W : Set (GenericSquare a))
    (hV : ResolvedBy (fun i => (U i).val) V) (hW : ResolvedBy (fun i => (U i).val) W) :
    resolvedPolygonMask U (V ∩ W) = resolvedPolygonMask U V ∩ resolvedPolygonMask U W := by
  ext ω
  obtain ⟨x,hx⟩ := ω.property
  obtain rfl : ω = ⟨polygonAssignment U x,⟨x,rfl⟩⟩ := Subtype.ext hx.symm
  have hVW : ResolvedBy (fun i => (U i).val) (V ∩ W) := by
    intro x y he
    exact and_congr (hV x y he) (hW x y he)
  simp only [Set.mem_inter_iff,resolvedPolygonMask_mem U _ hVW x,
    resolvedPolygonMask_mem U _ hV x,resolvedPolygonMask_mem U _ hW x]

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_intersection_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hfV : SmallControlled B.c f (B.fullGeometricSector hlarge P h V))
    (hfW : SmallControlled B.c f (B.fullGeometricSector hlarge P h W)) :
    SmallControlled B.c f (B.fullGeometricSector hlarge P h (V ⊓ W)) := by
  have hw := B.fullGeometricSector_whole hlarge P h
  unfold fullGeometricSector at hw hfV hfW ⊢
  change (B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) Set.univ) = _ at hw
  rw [resolvedPolygonMask_univ] at hw
  change SmallControlled _ _ ((B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) (V.val ∩ W.val)))
  rw [resolvedPolygonMask_inter _ _ _ hV hW]
  exact table_small_control_intersection _ B.c hw f _ _ hfV hfW

end InitialCoverSystem
end IntersectionControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ChartQuadrants
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

theorem coordinateRectangle_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u v : Fin 2 → CutRing)
    (huv : ∀ k, ordinary (u k) ≤ ordinary (v k))
    (hu : ∀ k, -ordinary r < ordinary (u k))
    (hv : ∀ k, ordinary (v k) < ordinary r)
    (hside : ∀ t : ℝ × ℝ,
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) →
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) → 0 ≤ cutForm a j t) :
    coordinateRectangle a u v ≤ clippedSlopePrimitive a r j := by
  intro p hp
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift u v huv
    (fun k => by have h1 := hu k; have h2 := hv k; linarith [hr.2]) p hp
  apply (mem_clippedSlope_lift r j hr p t ?_ ht).mpr
  · exact hside t hx hy
  · exact ⟨⟨(hu 0).trans_le hx.1,hx.2.trans (hv 0)⟩,
      ⟨(hu 1).trans_le hy.1,hy.2.trans (hv 1)⟩⟩

theorem coordinateRectangle_negative_sign {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (u v : Fin 2 → CutRing)
    (huv : ∀ k, ordinary (u k) ≤ ordinary (v k))
    (hu : ∀ k, -ordinary r < ordinary (u k))
    (hv : ∀ k, ordinary (v k) < ordinary r)
    (hside : ∀ t : ℝ × ℝ,
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) →
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) → cutForm a j t < 0) :
    coordinateRectangle a u v ≤ (clippedSlopePrimitive a r j)ᶜ := by
  intro p hp hpos
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift u v huv
    (fun k => by have h1 := hu k; have h2 := hv k; linarith [hr.2]) p hp
  have hR : (-ordinary r < t.1 ∧ t.1 < ordinary r) ∧
      (-ordinary r < t.2 ∧ t.2 < ordinary r) :=
    ⟨⟨(hu 0).trans_le hx.1,hx.2.trans (hv 0)⟩,
      ⟨(hu 1).trans_le hy.1,hy.2.trans (hv 1)⟩⟩
  have hh := (mem_clippedSlope_lift r j hr p t hR ht).mp hpos
  exact (not_lt_of_ge hh) (hside t hx hy)

end ChartQuadrants

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
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

section ChartTransforms

theorem spatialTranslate_mono {a : ℕ} (z : CutRing × CutRing)
    {U V : polygonAlgebra a} (h : U ≤ V) : spatialTranslate z U ≤ spatialTranslate z V :=
  fun _ hp => h hp

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentChartTemplates
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricCharts
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
section SymmetricCharts

theorem symmetricWindow_labels (s : CutRing) (j : Fin 2) :
    (symmetricWindowStart s j ≤ endpointLabel (-s) ∧
      endpointLabel (-s) < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel 0 ∧
      endpointLabel 0 < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel s ∧
      endpointLabel s < symmetricWindowStart s j+symmetricWindowLength s) := by
  have h₀ := Int.le_natAbs (a := endpointLabel s)
  have h₁ : -(endpointLabel s) ≤ ((endpointLabel s).natAbs:ℤ) := by
    simpa using (Int.le_natAbs (a := -endpointLabel s))
  simp only [symmetricWindowStart,symmetricWindowLength,endpointLabel_neg,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  change _ ∧ (_ ≤ (0:ℤ) ∧ (0:ℤ) < _) ∧ _
  omega

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_UniformTangentTransport
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

section ContainingChartWindow
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangentChartSector_eq_containing_window (hlarge : 15 < m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (n : ℕ) (g : B.CoordinateWindowLaw n) (p : Fin 2 → ℤ)
    (d : Fin 2) (e : Fin 5) (z : CutRing × CutRing)
    (hstart : ∀ j, p j ≤ pointLabel z j+q j)
    (hend : ∀ j, pointLabel z j+q j+k ≤ p j+n)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k) :
    B.fullGeometricSector hlarge
      (translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u e)) z) (h d e z)
      (spatialTranslate z (coordinateRectangle a l v)) =
    B.windowSector hlarge n g p (spatialTranslate z (coordinateRectangle a l v)) := by
  apply B.chartCoordinateSector_eq_window hlarge n g p
    _ (h d e z) Sum.inr Prod.fst (fun i => z+(coordinateWindowPrimitives k q i).2)
  · intro i
    rfl
  · intro i
    change p i.1 ≤ pointLabel (z+(coordinateWindowPrimitives k q i).2) i.1
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hh := hstart i.1
    omega
  · intro i
    change pointLabel (z+(coordinateWindowPrimitives k q i).2) i.1 < p i.1+(n-1:ℕ)
    simp only [pointLabel_add,coordinateWindow_pointLabel]
    have hi := i.2.isLt
    have hh := hend i.1
    omega
  · intro x y he
    apply (translatedTemplate_resolved (a := a) (r := r) (coordinateWindowPrimitives k q)
      (coordinateRectangle a l v) (fun x y he => and_congr
        (coordinateLabelWindow_resolved k q 0 (l 0) (v 0) (hl 0) (hv 0) x y he)
        (coordinateLabelWindow_resolved k q 1 (l 1) (v 1) (hl 1) (hv 1) x y he)) z) x y
    simpa only [primitiveTests,primitiveFamilyTests,translatedTemplate,coordinateWindowPrimitives,
      initialTest_coordinate] using he

theorem tangentSign_supported (hlarge : 15 < m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) :
    B.AlignedSmallSupported (B.tangentSign hlarge k q u h d z positive) := by
  unfold tangentSign
  apply B.fullGeometricSector_supported
  have hh := tangentChart_first_resolved (a := a) (r := r) (k := k) q d (signedShortSteps u 0) z
  cases positive with
  | false => exact fun x y he => not_congr (hh x y he)
  | true => exact hh

theorem tangentSign_control_from_rectangle (hlarge : 20 ≤ m+1)
    (k : ℕ) (q : Fin 2 → ℤ) (u : CutRing) (h : B.TangentChartLaws k q u)
    (n : ℕ) (g : B.CoordinateWindowLaw n) (p : Fin 2 → ℤ)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool)
    (hstart : ∀ j, p j ≤ pointLabel z j+q j)
    (hend : ∀ j, pointLabel z j+q j+k ≤ p j+n)
    (l v : Fin 2 → CutRing)
    (hl : ∀ j, q j ≤ endpointLabel (l j) ∧ endpointLabel (l j) < q j+k)
    (hv : ∀ j, q j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < q j+k)
    (hside : coordinateRectangle a l v ≤ if positive then clippedSlopePrimitive a r (slopeDirection d)
      else (clippedSlopePrimitive a r (slopeDirection d))ᶜ)
    (R : polygonAlgebra a) (hR : R ≤ spatialTranslate z (coordinateRectangle a l v))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n g p R)) :
    SmallControlled B.c f (B.tangentSign (by omega) k q u h d z positive) := by
  let P := translatedTemplate (tangentChartTemplate a k q d (signedShortSteps u 0)) z
  let V := spatialTranslate z (coordinateRectangle a l v)
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val :=
    tangentChart_rectangle_resolved q d _ z l v hl hv
  have he := B.tangentChartSector_eq_containing_window (by omega) k q u h n g p d 0 z hstart hend l v hl hv
  have hcV : SmallControlled B.c f (B.fullGeometricSector (by omega) P (h d 0 z) V) := by
    rw [he]
    refine B.control_trans hlarge f (B.windowSector (by omega) n g p R) _ hf ?_ hc ?_
    · rw [← he]
      exact B.fullGeometricSector_supported (by omega) P (h d 0 z) V hV
    · exact B.fullGeometricSector_small_control (by omega) _ _ R V hR
  apply B.control_trans hlarge f _ _ hf (B.tangentSign_supported (by omega) k q u h d z positive) hcV
  unfold tangentSign
  apply B.fullGeometricSector_small_control
  cases positive with
  | false => exact spatialTranslate_mono z hside
  | true => exact spatialTranslate_mono z hside

end InitialCoverSystem
end ContainingChartWindow

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteNestedLaw
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

section QuadrantControl

theorem signQuadrant_side {a : ℕ} (r s : CutRing)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (hs : 0 < ordinary s ∧ ordinary s < ordinary r) (d : Fin 2) (positive : Bool) :
    coordinateRectangle a (signQuadrantLower s d positive) (signQuadrantUpper s d positive) ≤
      if positive then clippedSlopePrimitive a r (slopeDirection d)
      else (clippedSlopePrimitive a r (slopeDirection d))ᶜ := by
  have hSlope : 0 ≤ Real.goldenRatio^a := pow_nonneg Real.goldenRatio_pos.le _
  cases positive with
  | true =>
    apply coordinateRectangle_sign r (slopeDirection d) hr
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower,signQuadrantUpper] <;> linarith [hs.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower] <;> linarith [hs.2,hr.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantUpper] <;> linarith [hs.2,hr.1]
    · intro t hx hy
      fin_cases d
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change 0 ≤ t.2-Real.goldenRatio^a*t.1
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hSlope hx.2.le).trans hy.1)
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change 0 ≤ t.1-Real.goldenRatio^a*t.2
        exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos hSlope hy.2.le).trans hx.1)
  | false =>
    apply coordinateRectangle_negative_sign r (slopeDirection d) hr
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower,signQuadrantUpper] <;> linarith [hs.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantLower] <;> linarith [hs.2,hr.1]
    · intro j; fin_cases d <;> fin_cases j <;> simp [signQuadrantUpper] <;> linarith [hs.2,hr.1]
    · intro t hx hy
      fin_cases d
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change t.2-Real.goldenRatio^a*t.1 < 0
        exact sub_neg.mpr (hy.2.trans_le (mul_nonneg hSlope hx.1))
      · simp [signQuadrantLower,signQuadrantUpper] at hx hy
        change t.1-Real.goldenRatio^a*t.2 < 0
        exact sub_neg.mpr (hx.2.trans_le (mul_nonneg hSlope hy.1))

theorem coordinateRectangle_mono {a : ℕ} (L V l v : Fin 2 → CutRing)
    (hL : ∀ j, ordinary (l j) ≤ ordinary (L j))
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hV : ∀ j, ordinary (V j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (l j) < 1) :
    coordinateRectangle a L V ≤ coordinateRectangle a l v := by
  exact inf_le_inf (coordinateInterval_mono 0 _ _ _ _ (hL 0) (hLV 0) (hV 0) (hlen 0))
    (coordinateInterval_mono 1 _ _ _ _ (hL 1) (hLV 1) (hV 1) (hlen 1))

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem rectangle_control_from_axes (hlarge : 15 < m+1)
    (n : ℕ) (g : B.CoordinateWindowLaw n)
    (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p q : Fin 2 → ℤ)
    (hp : ∀ j, q j ≤ p j) (hq : ∀ j, p j+t j ≤ q j+n)
    (L V : Fin 2 → CutRing)
    (hL : ∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j)
    (hV : ∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hc : ∀ j, SmallControlled B.c f
      (B.axisSector hlarge n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) :
    SmallControlled B.c f (B.windowSector hlarge n g q (coordinateRectangle a L V)) := by
  have hsmall (j : Fin 2) := axisInterval_resolved (a := a) (r := r)
    j (t j) (p j) (L j) (V j) (hL j) (hV j)
  have hlargeL (j : Fin 2) : q j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < q j+n := by
    have hh := hL j; have hh' := hp j; have hh'' := hq j; omega
  have hlargeV (j : Fin 2) : q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+n := by
    have hh := hV j; have hh' := hp j; have hh'' := hq j; omega
  have he (j : Fin 2) := B.axisSector_in_window hlarge n g j (t j) (ht j) (p j) q
    (hp j) (hq j) (coordinateInterval a j (L j) (V j)) (hsmall j)
  change SmallControlled B.c f (B.fullGeometricSector hlarge _ _
    (coordinateInterval a 0 (L 0) (V 0) ⊓ coordinateInterval a 1 (L 1) (V 1)))
  apply B.fullGeometricSector_intersection_control hlarge _ _ _ _
    (coordinateInterval_window n q 0 _ _ (hlargeL 0) (hlargeV 0))
    (coordinateInterval_window n q 1 _ _ (hlargeL 1) (hlargeV 1)) f
  · change SmallControlled B.c f (B.windowSector hlarge n g q (coordinateInterval a 0 (L 0) (V 0)))
    rw [← he 0]; exact hc 0
  · change SmallControlled B.c f (B.windowSector hlarge n g q (coordinateInterval a 1 (L 1) (V 1)))
    rw [← he 1]; exact hc 1

theorem tangentSign_quadrant_control (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    (n : ℕ) (g : B.CoordinateWindowLaw n)
    (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p q : Fin 2 → ℤ)
    (hp : ∀ j, q j ≤ p j) (hq : ∀ j, p j+t j ≤ q j+n)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool)
    (hstart : ∀ j, q j ≤ pointLabel z j+symmetricWindowStart s j)
    (hend : ∀ j, pointLabel z j+symmetricWindowStart s j+symmetricWindowLength s ≤ q j+n)
    (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hL : ∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j)
    (hV : ∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j)
    (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (L j))
    (hup : ∀ j, ordinary (V j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : ∀ j, SmallControlled B.c f
      (B.axisSector (by omega) n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) :
    SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
      (symmetricWindowStart s) u h d z positive) := by
  have hlab (j : Fin 2) :
      symmetricWindowStart s j ≤ endpointLabel (signQuadrantLower s d positive j) ∧
      endpointLabel (signQuadrantLower s d positive j) < symmetricWindowStart s j+symmetricWindowLength s := by
    unfold signQuadrantLower
    split <;> split <;> first | exact (symmetricWindow_labels s j).1 | exact (symmetricWindow_labels s j).2.1
  have hvab (j : Fin 2) :
      symmetricWindowStart s j ≤ endpointLabel (signQuadrantUpper s d positive j) ∧
      endpointLabel (signQuadrantUpper s d positive j) < symmetricWindowStart s j+symmetricWindowLength s := by
    unfold signQuadrantUpper
    split <;> split <;> first | exact (symmetricWindow_labels s j).2.1 | exact (symmetricWindow_labels s j).2.2
  apply B.tangentSign_control_from_rectangle hlarge _ _ u h n g q d z positive hstart hend
    _ _ hlab hvab (signQuadrant_side r s hr hs d positive) (coordinateRectangle a L V) ?_ f hf
    (B.rectangle_control_from_axes (by omega) n g t ht p q hp hq L V hL hV f hc)
  rw [spatialTranslate_coordinateRectangle]
  apply coordinateRectangle_mono L V _ _
  · intro j; simpa only [map_add,pointCoordinate] using hlo j
  · exact hLV
  · intro j; simpa only [map_add,pointCoordinate] using hup j
  · intro j
    simp only [map_add,add_sub_add_right_eq_sub]
    unfold signQuadrantUpper signQuadrantLower
    split <;> split <;> simp only [map_zero,map_neg] <;> linarith [hs.2,hr.2]

end InitialCoverSystem
end QuadrantControl

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

theorem rectangleCopy_quadrant_control_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u : CutRing) (hs : 0 < ordinary s ∧ ordinary s < ordinary r)
    (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u)
    {n : ℕ} (g : B.CoordinateWindowLaw n) (R : LabelledRectangle n)
    (d : Fin 2) (z : CutRing × CutRing) (positive : Bool) (fit : R.ChartFit s z)
    (hlo : ∀ j, ordinary (signQuadrantLower s d positive j)+ordinary (pointCoordinate z j) ≤ ordinary (R.lower j))
    (hup : ∀ j, ordinary (R.upper j) ≤ ordinary (signQuadrantUpper s d positive j)+ordinary (pointCoordinate z j)) :
    SmallControlled B.c (B.rectangleCopy (by omega) g R)
      (B.tangentSign (by omega) (symmetricWindowLength s) (symmetricWindowStart s) u h d z positive) :=
  B.tangentSign_quadrant_control hlarge hr s u hs h n g R.length R.length_le R.start
    fit.window fit.source_start fit.source_end d z positive fit.chart_start fit.chart_end
    R.lower R.upper R.ordered R.lower_label R.upper_label hlo hup _
    (B.rectangleCopy_supported (by omega) g R) (B.rectangleCopy_axes_control (by omega) g R)

end InitialCoverSystem
end OldRectangles

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control_oai := @OAI.SimpleAmenable.InitialCoverSystem.rectangleCopy_quadrant_control_oai
