-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:01:51.94553+00:00
-- url     : https://prove2.me/submissions/4a9f98ac-25dc-41b0-9f79-17f61c5492d9

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

end CircularIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section AxisWindows

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_overlap_control (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n) (p q z : ℤ)
    (hsp : z ≤ p) (hep : p+(k:ℤ) ≤ z+n)
    (hsq : z ≤ q) (heq : q+(l:ℤ) ≤ z+n) (V W : polygonAlgebra a) (hVW : V ≤ W)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j l q) i).val) W.val) :
    SmallControlled B.c (B.axisSector hlarge n h j k hk p V)
      (B.axisSector hlarge n h j l hl q W) := by
  rw [B.axisSector_in_window hlarge n h j k hk p (fun _ => z) hsp hep V hV,
    B.axisSector_in_window hlarge n h j l hl q (fun _ => z) hsq heq W hW]
  exact B.fullGeometricSector_small_control hlarge _ _ V W hVW

end InitialCoverSystem
end AxisWindows

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowEnclosureGeometry
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
section WindowEnclosureGeometry

theorem integer_window_path (p q : ℤ) (S : ℕ) (hS : 1 ≤ S) :
    ∃ T : ℕ, ∃ w : ℕ → ℤ,
      w 0 = p ∧ w T = q ∧
      T ≤ (q-p).natAbs / S + 1 ∧
      (∀ i, |w (i+1)-w i| ≤ (S:ℤ)) ∧
      ∀ i, min p q ≤ w i ∧ w i ≤ max p q := by
  suffices h : ∀ p q : ℤ, p ≤ q →
      ∃ T : ℕ, ∃ w : ℕ → ℤ,
        w 0 = p ∧ w T = q ∧ T ≤ (q-p).natAbs / S + 1 ∧
        (∀ i, |w (i+1)-w i| ≤ (S:ℤ)) ∧
        ∀ i, p ≤ w i ∧ w i ≤ q by
    by_cases hpq : p ≤ q
    · obtain ⟨T,w,h₀,hT,hb,hs,hw⟩ := h p q hpq
      exact ⟨T,w,h₀,hT,hb,hs,fun i => by simpa [hpq] using hw i⟩
    · have hqp : q ≤ p := le_of_not_ge hpq
      obtain ⟨T,w,h₀,hT,hb,hs,hw⟩ := h (-p) (-q) (by omega)
      refine ⟨T,fun i => -w i,by simp [h₀],by simp [hT],?_,?_,?_⟩
      · have he : -q - -p = -(q-p) := by ring
        rw [he,Int.natAbs_neg] at hb
        exact hb
      · intro i
        simpa only [neg_sub_neg,abs_sub_comm] using hs i
      · intro i
        simp only [min_eq_right hqp,max_eq_left hqp]
        constructor <;> linarith [(hw i).1,(hw i).2]
  intro p q hpq
  let D := (q-p).toNat
  have hD : (D:ℤ) = q-p := Int.toNat_of_nonneg (by omega)
  let T := D/S+1
  let w : ℕ → ℤ := fun i => p + (min (i*S) D : ℕ)
  have hTS : D ≤ T*S := by
    have hd : D/S*S ≤ D := Nat.div_mul_le_self D S
    have hr : D%S < S := Nat.mod_lt D (by omega)
    have he := Nat.mod_add_div D S
    rw [Nat.mul_comm S (D/S)] at he
    dsimp [T]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  refine ⟨T,w,by simp [w],?_,?_,?_,?_⟩
  · simp only [w,Nat.min_eq_right hTS]
    omega
  · dsimp [T,D]
    have he : (q-p).toNat = (q-p).natAbs := by
      have ha := Int.natAbs_of_nonneg (show 0 ≤ q-p by omega)
      omega
    rw [he]
  · intro i
    have ha : min (i*S) D ≤ min ((i+1)*S) D :=
      min_le_min_right D (Nat.mul_le_mul_right S (by omega))
    have hb : min ((i+1)*S) D ≤ min (i*S) D + S := by
      by_cases hi : i*S ≤ D
      · rw [Nat.min_eq_left hi,Nat.add_mul,Nat.one_mul]
        exact min_le_left _ _
      · rw [Nat.min_eq_right (le_of_not_ge hi)]
        omega
    change |(p+(min ((i+1)*S) D : ℕ):ℤ) - (p+(min (i*S) D : ℕ))| ≤ S
    rw [add_sub_add_left_eq_sub,abs_of_nonneg (by exact sub_nonneg.mpr (by exact_mod_cast ha) :
      (0:ℤ) ≤ (min ((i+1)*S) D : ℕ) - (min (i*S) D : ℕ))]
    apply sub_le_iff_le_add.mpr
    have hb' : ((min ((i+1)*S) D : ℕ):ℤ) ≤ ((min (i*S) D : ℕ):ℤ) + (S:ℤ) := by
      exact_mod_cast hb
    simpa only [add_comm] using hb'
  · intro i
    dsimp [w]
    have hi := min_le_right (i*S) D
    constructor <;> omega

end WindowEnclosureGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_WindowEnclosureChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowEnclosureChains

theorem lowerEnclosure_label (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    q k ≤ endpointLabel (lowerEnclosure n hn q a k) ∧
      endpointLabel (lowerEnclosure n hn q a k) < q k+n := by
  cases k with
  | zero => exact (windowBracket n hn (q 0) a).lower_label
  | succ k => exact (windowBracket n hn (q (k+1)) _).lower_label

theorem upperEnclosure_label (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    q k ≤ endpointLabel (upperEnclosure n hn q b k) ∧
      endpointLabel (upperEnclosure n hn q b k) < q k+n := by
  cases k with
  | zero => exact (windowBracket n hn (q 0) b).upper_label
  | succ k => exact (windowBracket n hn (q (k+1)) _).upper_label

theorem lowerEnclosure_step (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    ordinary (lowerEnclosure n hn q a k) - 201/(n:ℝ) ≤
        ordinary (lowerEnclosure n hn q a (k+1)) ∧
      ordinary (lowerEnclosure n hn q a (k+1)) < ordinary (lowerEnclosure n hn q a k) :=
  ⟨(windowBracket n hn (q (k+1)) _).lower_bound,
    (windowBracket n hn (q (k+1)) _).lower_lt⟩

theorem upperEnclosure_step (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    ordinary (upperEnclosure n hn q b k) < ordinary (upperEnclosure n hn q b (k+1)) ∧
      ordinary (upperEnclosure n hn q b (k+1)) ≤
        ordinary (upperEnclosure n hn q b k) + 201/(n:ℝ) :=
  ⟨(windowBracket n hn (q (k+1)) _).upper_lt,
    (windowBracket n hn (q (k+1)) _).upper_bound⟩

theorem lowerEnclosure_bounds (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a : ℝ) (k : ℕ) :
    a - ((k:ℝ)+1)*201/(n:ℝ) ≤ ordinary (lowerEnclosure n hn q a k) ∧
      ordinary (lowerEnclosure n hn q a k) < a := by
  induction k with
  | zero =>
    simpa [lowerEnclosure] using And.intro (windowBracket n hn (q 0) a).lower_bound
      (windowBracket n hn (q 0) a).lower_lt
  | succ k ih =>
    have hs := lowerEnclosure_step n hn q a k
    constructor
    · simp only [Nat.cast_add,Nat.cast_one]
      have he : ((k:ℝ)+1+1)*201/(n:ℝ) = ((k:ℝ)+1)*201/(n:ℝ) + 201/(n:ℝ) := by ring
      rw [he]
      linarith [ih.1,hs.1]
    · exact lt_trans hs.2 ih.2

theorem upperEnclosure_bounds (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (b : ℝ) (k : ℕ) :
    b < ordinary (upperEnclosure n hn q b k) ∧
      ordinary (upperEnclosure n hn q b k) ≤ b + ((k:ℝ)+1)*201/(n:ℝ) := by
  induction k with
  | zero =>
    simpa [upperEnclosure] using And.intro (windowBracket n hn (q 0) b).upper_lt
      (windowBracket n hn (q 0) b).upper_bound
  | succ k ih =>
    have hs := upperEnclosure_step n hn q b k
    constructor
    · exact lt_trans ih.1 hs.1
    · simp only [Nat.cast_add,Nat.cast_one]
      have he : ((k:ℝ)+1+1)*201/(n:ℝ) = ((k:ℝ)+1)*201/(n:ℝ) + 201/(n:ℝ) := by ring
      rw [he]
      linarith [ih.2,hs.2]

theorem window_enclosure_chain (n : ℕ) (hn : 1 ≤ n) (q : ℕ → ℤ) (a b : ℝ)
    (_hab : a ≤ b) :
    ∃ u v : ℕ → CutRing,
      (∀ k, (q k ≤ endpointLabel (u k) ∧ endpointLabel (u k) < q k+n) ∧
        (q k ≤ endpointLabel (v k) ∧ endpointLabel (v k) < q k+n)) ∧
      (∀ k, Set.Icc a b ⊆ Set.Ioo (ordinary (u k)) (ordinary (v k))) ∧
      (∀ k, Set.Icc (ordinary (u k)) (ordinary (v k)) ⊆
        Set.Ioo (ordinary (u (k+1))) (ordinary (v (k+1)))) ∧
      ∀ k : ℕ, a-((k:ℝ)+1)*201/(n:ℝ) ≤ ordinary (u k) ∧
        ordinary (v k) ≤ b+((k:ℝ)+1)*201/(n:ℝ) := by
  refine ⟨lowerEnclosure n hn q a,upperEnclosure n hn q b,?_,?_,?_,?_⟩
  · intro k
    exact ⟨lowerEnclosure_label n hn q a k,upperEnclosure_label n hn q b k⟩
  · intro k x hx
    exact ⟨lt_of_lt_of_le (lowerEnclosure_bounds n hn q a k).2 hx.1,
      lt_of_le_of_lt hx.2 (upperEnclosure_bounds n hn q b k).1⟩
  · intro k x hx
    exact ⟨lt_of_lt_of_le (lowerEnclosure_step n hn q a k).2 hx.1,
      lt_of_le_of_lt hx.2 (upperEnclosure_step n hn q b k).1⟩
  · intro k
    exact ⟨(lowerEnclosure_bounds n hn q a k).1,(upperEnclosure_bounds n hn q b k).2⟩

end WindowEnclosureChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_UniformPropagationBounds
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section OldWindowBridgeGeometry

theorem short_window_scale (n : ℕ) (hn : 160 ≤ n) :
    1 ≤ n/8 ∧ 1 ≤ (n/8)/2 ∧ (n:ℝ)/9 ≤ (n/8:ℕ) ∧
      (n:ℝ)/20 ≤ ((n/8)/2:ℕ) ∧
      (n/8:ℕ) + ((n/8)/2:ℕ) ≤ n/4 := by
  have h₁ := Nat.mod_add_div n 8
  have h₂ := Nat.mod_lt n (by norm_num : 0 < 8)
  have h₃ := Nat.mod_add_div (n/8) 2
  have h₄ := Nat.mod_lt (n/8) (by norm_num : 0 < 2)
  have h₅ := Nat.mod_add_div n 4
  have h₆ := Nat.mod_lt n (by norm_num : 0 < 4)
  have ha : n ≤ 9*(n/8) := by omega
  have hb : n ≤ 20*((n/8)/2) := by omega
  refine ⟨by omega,by omega,?_,?_,by omega⟩
  · have : (n:ℝ) ≤ 9*(n/8:ℕ) := by exact_mod_cast ha
    linarith
  · have : (n:ℝ) ≤ 20*((n/8)/2:ℕ) := by exact_mod_cast hb
    linarith

theorem short_window_path {K : ℝ} (_hK : 0 ≤ K) (n : ℕ) (hn : 160 ≤ n)
    (p q : ℤ) (hpq : ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) :
    ∃ T : ℕ, ∃ w : ℕ → ℤ,
      w 0 = p ∧ w T = q ∧ (T:ℝ) ≤ 20*(K+2) ∧
      (∀ i, |w (i+1)-w i| ≤ (((n/8)/2:ℕ):ℤ)) ∧
      ∀ i, min p q ≤ w i ∧ w i ≤ max p q := by
  obtain ⟨_,hS,_,hSn,_⟩ := short_window_scale n hn
  obtain ⟨T,w,h₀,hT,hbound,hstep,hrange⟩ := integer_window_path p q ((n/8)/2) hS
  refine ⟨T,w,h₀,hT,?_,hstep,hrange⟩
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS0 : (0:ℝ) < ((n/8)/2:ℕ) := by exact_mod_cast hS
  have hdiv : (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) ≤ 20*(K+1) := by
    have hmul : (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) * ((n/8)/2:ℕ) ≤
        ((q-p).natAbs:ℝ) := by exact_mod_cast Nat.div_mul_le_self (q-p).natAbs ((n/8)/2)
    have hfloor : (0:ℝ) ≤ (((q-p).natAbs / ((n/8)/2):ℕ):ℝ) := by positivity
    nlinarith
  have hb : (T:ℝ) ≤ (((q-p).natAbs / ((n/8)/2):ℕ):ℝ)+1 := by exact_mod_cast hbound
  linarith

theorem old_window_bridge_geometry {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ)
    (B : ℕ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p q : ℤ,
      ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ) → ∀ a b : ℝ, a ≤ b →
      ∃ T : ℕ, ∃ w : ℕ → ℤ, ∃ u v : ℕ → CutRing,
        w 0 = p ∧ w T = q ∧ (T:ℝ) ≤ 20*(K+2) ∧
        (∀ i, (w i ≤ endpointLabel (u i) ∧ endpointLabel (u i) < w i+(n/8:ℕ)) ∧
          (w i ≤ endpointLabel (v i) ∧ endpointLabel (v i) < w i+(n/8:ℕ))) ∧
        (∀ i, |w (i+1)-w i| + (n/8:ℕ) + (2*B:ℕ) < (n:ℤ)) ∧
        (∀ i, Set.Icc a b ⊆ Set.Ioo (ordinary (u i)) (ordinary (v i))) ∧
        (∀ i, Set.Icc (ordinary (u i)) (ordinary (v i)) ⊆
          Set.Ioo (ordinary (u (i+1))) (ordinary (v (i+1)))) ∧
        ∀ i, i ≤ T → Set.Icc (ordinary (u i)) (ordinary (v i)) ⊆
          Set.Ioo (a-δ) (b+δ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 160 (max (40*(B:ℝ))
    ((20*(K+2)+1)*201*9/δ)))
  have hN160 : 160 ≤ N := by
    have : (160:ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (le_of_lt this)
  refine ⟨N,hN160,fun n hn p q hpq a b hab => ?_⟩
  have hn160 : 160 ≤ n := hN160.trans hn
  have hnr : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnB : 40*(B:ℝ) < n := lt_of_lt_of_le
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN) hnr
  have hnδ : (20*(K+2)+1)*201*9/δ < (n:ℝ) := lt_of_lt_of_le
    (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN) hnr
  obtain ⟨hL,_,hLn,_,hLS⟩ := short_window_scale n hn160
  obtain ⟨T,w,h₀,hT,hbound,hstep,hrange⟩ := short_window_path hK n hn160 p q hpq
  obtain ⟨u,v,hlabel,hinc,hnest,herror⟩ := window_enclosure_chain (n/8) hL w a b hab
  refine ⟨T,w,u,v,h₀,hT,hbound,hlabel,?_,hinc,hnest,?_⟩
  · intro i
    have hBn : 40*B < n := by exact_mod_cast hnB
    have hspan : (n/8)+((n/8)/2)+2*B < n := by omega
    have hspan' : ((n/8:ℕ):ℤ)+(((n/8)/2:ℕ):ℤ)+(2*B:ℕ) < (n:ℤ) := by exact_mod_cast hspan
    linarith [hstep i]
  · intro i hi x hx
    have hiT : (i:ℝ) ≤ T := by exact_mod_cast hi
    have hL0 : (0:ℝ) < (n/8:ℕ) := by exact_mod_cast hL
    have hb₀ : 0 ≤ 20*(K+2)+1 := by linarith
    have he : ((i:ℝ)+1)*201/(n/8:ℕ) < δ := by
      apply (div_lt_iff₀ hL0).mpr
      have hd : (20*(K+2)+1)*201*9 < (n:ℝ)*δ := (div_lt_iff₀ hδ).mp hnδ
      nlinarith
    exact ⟨by linarith [(herror i).1,hx.1],by linarith [(herror i).2,hx.2]⟩

end OldWindowBridgeGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ControlCalculus
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem control_chain (hlarge : 20 ≤ m+1)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (F : ℕ → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (T : ℕ) (hf : B.AlignedSmallSupported f)
    (hF : ∀ i, i ≤ T → B.AlignedSmallSupported (F i))
    (h₀ : SmallControlled B.c f (F 0))
    (hstep : ∀ i, i < T → SmallControlled B.c (F i) (F (i+1))) :
    SmallControlled B.c f (F T) := by
  have hh : ∀ i, i ≤ T → SmallControlled B.c f (F i) := by
    intro i
    induction i with
    | zero => intro _; exact h₀
    | succ i ih =>
      intro hi
      exact B.control_trans hlarge f (F i) (F (i+1)) hf (hF _ (by omega))
        (ih (by omega)) (hstep i (by omega))
  exact hh T le_rfl

theorem axisSector_supported (hlarge : 15 < m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j k p) i).val) V.val) :
    B.AlignedSmallSupported (B.axisSector hlarge n h j k hk p V) :=
  B.fullGeometricSector_supported hlarge _ _ V hV

theorem axisInterval_chain_control (hlarge : 20 ≤ m+1) (n : ℕ) (h : B.CoordinateWindowLaw n)
    (j : Fin 2) (k : ℕ) (hk : k ≤ n) (T : ℕ) (w : ℕ → ℤ) (u v : ℕ → CutRing)
    (hlabel : ∀ i, (w i ≤ endpointLabel (u i) ∧ endpointLabel (u i) < w i+k) ∧
      (w i ≤ endpointLabel (v i) ∧ endpointLabel (v i) < w i+k))
    (hstep : ∀ i, i < T → |w (i+1)-w i|+(k:ℤ) ≤ n)
    (hinc : ∀ i, i < T → coordinateInterval a j (u i) (v i) ≤
      coordinateInterval a j (u (i+1)) (v (i+1)))
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (h₀ : SmallControlled B.c f (B.axisSector (by omega) n h j k hk (w 0)
      (coordinateInterval a j (u 0) (v 0)))) :
    SmallControlled B.c f (B.axisSector (by omega) n h j k hk (w T)
      (coordinateInterval a j (u T) (v T))) := by
  apply B.control_chain hlarge f
    (fun i => B.axisSector (by omega) n h j k hk (w i) (coordinateInterval a j (u i) (v i))) T hf
  · intro i _
    exact B.axisSector_supported (by omega) n h j k hk (w i) _
      (axisInterval_resolved j k (w i) (u i) (v i) (hlabel i).1 (hlabel i).2)
  · exact h₀
  · intro i hi
    have hh := hstep i hi
    have h₁ := le_abs_self (w (i+1)-w i)
    have h₂ := neg_le_abs (w (i+1)-w i)
    apply B.axisSector_overlap_control (by omega) n h j k k hk hk (w i) (w (i+1))
      (min (w i) (w (i+1))) (min_le_left _ _) ?_ (min_le_right _ _) ?_ _ _ (hinc i hi)
      (axisInterval_resolved j k (w i) (u i) (v i) (hlabel i).1 (hlabel i).2)
      (axisInterval_resolved j k (w (i+1)) (u (i+1)) (v (i+1)) (hlabel (i+1)).1 (hlabel (i+1)).2)
    · omega
    · omega

end InitialCoverSystem
end SourceControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntersectionControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoverUniformBridges
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem old_axis_bridge_control_cover_uniform (hlarge : 20 ≤ m+1) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (j : Fin 2) (s : ℕ) (hs : s ≤ n) (p q : ℤ),
      ((q-p).natAbs:ℝ) ≤ (K+1)*(n:ℝ) →
      ∀ u v U V : CutRing, ordinary u ≤ ordinary v →
      ordinary U ≤ ordinary u-δ → ordinary v+δ ≤ ordinary V →
      ordinary V-ordinary U < 1 →
      (p ≤ endpointLabel u ∧ endpointLabel u < p+s) →
      (p ≤ endpointLabel v ∧ endpointLabel v < p+s) →
      (q ≤ endpointLabel U ∧ endpointLabel U < q+(n/8:ℕ)) →
      (q ≤ endpointLabel V ∧ endpointLabel V < q+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      SmallControlled B.c f (B.axisSector (by omega) n h j s hs p (coordinateInterval a j u v)) →
      SmallControlled B.c f (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q
        (coordinateInterval a j U V)) := by
  obtain ⟨N,hN,hgeo⟩ := old_window_bridge_geometry hK hδ 0
  refine ⟨N,hN,?_⟩
  intro M B n hn h j s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
  obtain ⟨T,w,u',v',hw₀,hwT,_,hlabel,hstep,hinc,hnest,herror⟩ :=
    hgeo n hn p q hpq (ordinary u) (ordinary v) huv
  have horder (i : ℕ) : ordinary (u' i) ≤ ordinary (v' i) := by
    have hh := hinc i (show ordinary u ∈ Set.Icc (ordinary u) (ordinary v) from ⟨le_rfl,huv⟩)
    exact hh.1.le.trans hh.2.le
  have hbounds (i : ℕ) (hi : i ≤ T) :
      ordinary U ≤ ordinary (u' i) ∧ ordinary (v' i) ≤ ordinary V := by
    have h₁ := herror i hi (show ordinary (u' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
      from ⟨le_rfl,horder i⟩)
    have h₂ := herror i hi (show ordinary (v' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
      from ⟨horder i,le_rfl⟩)
    exact ⟨hU.trans h₁.1.le,h₂.2.le.trans hV⟩
  have hlength (i : ℕ) (hi : i ≤ T) : ordinary (v' i)-ordinary (u' i) < 1 := by
    obtain ⟨h₁,h₂⟩ := hbounds i hi
    linarith
  have hlabels₀ : (p ≤ endpointLabel (u' 0) ∧ endpointLabel (u' 0) < p+(n/8:ℕ)) ∧
      (p ≤ endpointLabel (v' 0) ∧ endpointLabel (v' 0) < p+(n/8:ℕ)) := by
    simpa only [hw₀] using hlabel 0
  have hfirstinc : coordinateInterval a j u v ≤ coordinateInterval a j (u' 0) (v' 0) := by
    apply coordinateInterval_mono j u v (u' 0) (v' 0)
    · exact (hinc 0 (show ordinary u ∈ Set.Icc (ordinary u) (ordinary v) from ⟨le_rfl,huv⟩)).1.le
    · exact huv
    · exact (hinc 0 (show ordinary v ∈ Set.Icc (ordinary u) (ordinary v) from ⟨huv,le_rfl⟩)).2.le
    · exact hlength 0 (Nat.zero_le _)
  have hfirst := B.axisSector_overlap_control (by omega : 15 < m+1) n h j s (n/8) hs
    (Nat.div_le_self n 8) p p p le_rfl (by omega) le_rfl
    (by omega)
    (coordinateInterval a j u v) (coordinateInterval a j (u' 0) (v' 0)) hfirstinc
    (axisInterval_resolved j s p u v hlu hlv)
    (axisInterval_resolved j (n/8) p (u' 0) (v' 0) hlabels₀.1 hlabels₀.2)
  have hF₀ := B.axisSector_supported (by omega : 15 < m+1) n h j (n/8)
    (Nat.div_le_self n 8) p (coordinateInterval a j (u' 0) (v' 0))
    (axisInterval_resolved j (n/8) p (u' 0) (v' 0) hlabels₀.1 hlabels₀.2)
  have h₀ := B.control_trans hlarge f _ _ hf hF₀ hstart hfirst
  have hchain : SmallControlled B.c f (B.axisSector (by omega) n h j (n/8)
      (Nat.div_le_self n 8) (w T) (coordinateInterval a j (u' T) (v' T))) := by
    refine B.axisInterval_chain_control hlarge n h j (n/8) (Nat.div_le_self n 8) T w u' v'
      hlabel ?_ ?_ f hf ?_
    · intro i _
      have hh := hstep i
      simp only [mul_zero,Nat.cast_zero,add_zero] at hh
      exact hh.le
    · intro i hi
      apply coordinateInterval_mono j (u' i) (v' i) (u' (i+1)) (v' (i+1))
      · exact (hnest i (show ordinary (u' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
          from ⟨le_rfl,horder i⟩)).1.le
      · exact horder i
      · exact (hnest i (show ordinary (v' i) ∈ Set.Icc (ordinary (u' i)) (ordinary (v' i))
          from ⟨horder i,le_rfl⟩)).2.le
      · exact hlength (i+1) (by omega)
    · simpa only [hw₀] using h₀
  rw [hwT] at hchain
  have hlastinc : coordinateInterval a j (u' T) (v' T) ≤ coordinateInterval a j U V :=
    coordinateInterval_mono j (u' T) (v' T) U V (hbounds T le_rfl).1 (horder T)
      (hbounds T le_rfl).2 hlen
  have hlast : SmallControlled B.c
      (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q (coordinateInterval a j (u' T) (v' T)))
      (B.axisSector (by omega) n h j (n/8) (Nat.div_le_self n 8) q (coordinateInterval a j U V)) :=
    B.fullGeometricSector_small_control (by omega) _ _ _ _ hlastinc
  exact B.control_trans hlarge f _ _ hf
    (B.axisSector_supported (by omega) n h j (n/8) (Nat.div_le_self n 8) q _
      (axisInterval_resolved j (n/8) q U V hlU hlV)) hchain hlast

theorem old_rectangle_bridge_control_cover_uniform_oai (hlarge : 20 ≤ m+1)
    {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M), ∀ n : ℕ, N ≤ n → ∀ h : B.CoordinateWindowLaw n,
      ∀ (s : Fin 2 → ℕ) (hs : ∀ j, s j ≤ n) (p q : Fin 2 → ℤ),
      (∀ j, ((q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) →
      ∀ u v U V : Fin 2 → CutRing,
      (∀ j, ordinary (u j) ≤ ordinary (v j)) →
      (∀ j, ordinary (U j) ≤ ordinary (u j)-δ) →
      (∀ j, ordinary (v j)+δ ≤ ordinary (V j)) →
      (∀ j, ordinary (V j)-ordinary (U j) < 1) →
      (∀ j, p j ≤ endpointLabel (u j) ∧ endpointLabel (u j) < p j+s j) →
      (∀ j, p j ≤ endpointLabel (v j) ∧ endpointLabel (v j) < p j+s j) →
      (∀ j, q j ≤ endpointLabel (U j) ∧ endpointLabel (U j) < q j+(n/8:ℕ)) →
      (∀ j, q j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < q j+(n/8:ℕ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n h j (s j) (hs j) (p j) (coordinateInterval a j (u j) (v j)))) →
      SmallControlled B.c f (B.windowSector (by omega) n h q (coordinateRectangle a U V)) := by
  obtain ⟨N,hN,hbridge⟩ := old_axis_bridge_control_cover_uniform (a := a) (r := r) (hm := hm) hlarge hK hδ
  refine ⟨N,hN,?_⟩
  intro M B n hn h s hs p q hpq u v U V huv hU hV hlen hlu hlv hlU hlV f hf hstart
  have hc (j : Fin 2) : SmallControlled B.c f
      (B.windowSector (by omega) n h q (coordinateInterval a j (U j) (V j))) := by
    have hh := hbridge M B n hn h j (s j) (hs j) (p j) (q j) (hpq j)
      (u j) (v j) (U j) (V j) (huv j) (hU j) (hV j) (hlen j)
      (hlu j) (hlv j) (hlU j) (hlV j) f hf (hstart j)
    rw [B.axisSector_in_window (by omega) n h j (n/8) (Nat.div_le_self n 8)
      (q j) q le_rfl (by omega) (coordinateInterval a j (U j) (V j))
      (axisInterval_resolved j (n/8) (q j) (U j) (V j) (hlU j) (hlV j))] at hh
    exact hh
  apply B.fullGeometricSector_intersection_control (by omega) (coordinateWindowPrimitives n q)
    (fun I _ b hb => h I b hb q) (coordinateInterval a 0 (U 0) (V 0))
    (coordinateInterval a 1 (U 1) (V 1)) ?_ ?_ f (hc 0) (hc 1)
  · exact coordinateLabelWindow_resolved n q 0 (U 0) (V 0)
      ⟨(hlU 0).1,by have h' := (hlU 0).2; omega⟩
      ⟨(hlV 0).1,by have h' := (hlV 0).2; omega⟩
  · exact coordinateLabelWindow_resolved n q 1 (U 1) (V 1)
      ⟨(hlU 1).1,by have h' := (hlU 1).2; omega⟩
      ⟨(hlV 1).1,by have h' := (hlV 1).2; omega⟩

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform_oai := @OAI.SimpleAmenable.InitialCoverSystem.old_rectangle_bridge_control_cover_uniform_oai
