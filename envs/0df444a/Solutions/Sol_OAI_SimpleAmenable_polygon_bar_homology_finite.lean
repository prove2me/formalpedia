-- Prove2me | solution 1 for OAI.SimpleAmenable.polygon_bar_homology_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:10:04.215487+00:00
-- url     : https://prove2.me/submissions/74257dbe-c378-4ab7-8bad-89542eecd06f

import Mathlib
import Definitions.Def_OAIQ65Sa021
import Theorems.Thm_OAI_IntervalBar_Diagram_bar_finite_of_triple
import Theorems.Thm_OAI_SimpleAmenable_SymmetricConfiguration_triple_homology_finite

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_ConcurrentDenominators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PolygonAtomLaw
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAtomLaw
variable {a m : ℕ} {Ω : Type*}

@[simp] theorem PolygonLabelling.tableHom_single_mask [Fintype Ω] (v : PolygonLabelling a Ω)
    (ω : Ω) : v.tableHom.comp (sectorMask {ω}) = conditionalAlternatingHom (m := m) (v.fiber ω) := by
  classical
  ext s : 1
  change v.tableHom (sectorMask {ω} s) = conditionalAlternatingHom (v.fiber ω) s
  have he : sectorMask {ω} s = Pi.mulSingle ω s := by
    ext ν
    by_cases hh : ν=ω <;> simp [sectorMask,hh]
  rw [he,v.tableHom_single]

end PolygonAtomLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

lemma finite_of_ker_le [IsNoetherianRing R] (f : A →ₗ[R] B) (g : A →ₗ[R] E)
    (hf : Function.Surjective f) (hker : LinearMap.ker g ≤ LinearMap.ker f)
    [Module.Finite R E] : Module.Finite R B := by
  have : Module.Finite R (LinearMap.range g) :=
    Module.Finite.of_injective (LinearMap.range g).subtype Subtype.val_injective
  have : Module.Finite R (A ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  let φ := (LinearMap.ker g).liftQ f hker
  exact Module.Finite.of_surjective φ (by
    intro b
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨(LinearMap.ker g).mkQ a,rfl⟩)

namespace Data
variable (K : Data (R:=R) (A:=A) (B:=B) (C:=C))

lemma filtration_mono : Monotone K.filtration := by
  intro p q hpq y hy
  obtain ⟨x,rfl⟩ := hy
  exact ⟨⟨x.val,K.monoB hpq x.property⟩,rfl⟩

variable [IsNoetherianRing R]

lemma finite_step (p : ℤ) [Module.Finite R (K.filtration (p-1))]
    [Module.Finite R (K.E₂ p)] : Module.Finite R (K.filtration p) := by
  let S : Submodule R (K.filtration p) :=
    (K.filtration (p-1)).submoduleOf (K.filtration p)
  have : Module.Finite R S := Module.Finite.equiv
    (Submodule.submoduleOfEquivOfLe (K.filtration_mono (by omega : p-1≤p))).symm
  let f : K.cycles p →ₗ[R] (K.filtration p ⧸ S) := S.mkQ.comp (K.πp p).rangeRestrict
  have hf : Function.Surjective f := (Submodule.mkQ_surjective S).comp
    (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
  have hk : LinearMap.ker (K.lead p) ≤ LinearMap.ker f := by
    intro x hx
    change f x=0
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    exact K.lower_of_lead_zero x hx
  have : Module.Finite R (K.filtration p ⧸ S) := finite_of_ker_le f (K.lead p) hf hk
  exact Module.Finite.of_submodule_quotient S

lemma finite_H (N : ℕ) (hzero : K.FB 0=⊥) (htop : K.FB (N+1)=⊤)
    (hfinite : ∀ p : ℕ, p≤N → Module.Finite R (K.E₂ (p+1))) : Module.Finite R K.H := by
  have hz : K.filtration 0=⊥ := by
    apply le_antisymm _ bot_le
    rintro y ⟨x,rfl⟩
    have hx : x=0 := by
      apply Subtype.ext; apply Subtype.ext
      exact (Submodule.mem_bot R).mp (hzero ▸ x.property)
    rw [hx,map_zero]
    exact Submodule.zero_mem _
  have hfg : ∀ p : ℕ, p≤N+1 → Module.Finite R (K.filtration p) := by
    intro p hp
    induction p with
    | zero => rw [Nat.cast_zero,hz]; infer_instance
    | succ p ih =>
      have := ih (by omega)
      have := hfinite p (by omega)
      have he : (p:ℤ)+1-1=(p:ℤ) := by omega
      have : Module.Finite R (K.filtration ((p:ℤ)+1-1)) := by rw [he]; infer_instance
      exact K.finite_step (p+1)
  have hh : K.filtration (N+1)=⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.dCycles) y
    exact ⟨⟨z,by change z.val∈K.FB (N+1); rw [htop]; trivial⟩,rfl⟩
  have := hfg (N+1) le_rfl
  exact Module.Finite.of_surjective (K.filtration ((N+1:ℕ):ℤ)).subtype (by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    have he : ((N+1:ℕ):ℤ)=(N:ℤ)+1 := by omega
    rw [he,hh]
    trivial)

end Data
end FilteredFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Boundary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading

universe u
variable {R : Type u} [CommRing R]
open TotalProjection
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma finite_E₂ [IsNoetherianRing R] (p q : ℕ)
    [Module.Finite R (ConcreteHomology.H (row K q) p)] :
    Module.Finite R ((filteredData K (p+q)).E₂ ((p:ℤ)+1)) := by
  apply FilteredFiniteness.finite_of_ker_le
    (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
      ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).mkQ (lead K p q)
    (Submodule.mkQ_surjective _)
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (lead_zero_boundary K p q x hx)

lemma finite_total_concrete [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R (ConcreteHomology.H (K.total c) n) := by
  change Module.Finite R (filteredData K n).H
  apply FilteredFiniteness.Data.finite_H _ n (filtration_zero K n) (filtration_top K n)
  intro p hp
  have hn : p+(n-p)=n := Nat.add_sub_of_le hp
  have := hfinite p (n-p) hn
  have h := finite_E₂ K p (n-p)
  rwa [hn] at h

lemma finite_total [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R (ConcreteHomology.H (row K q) p)) :
    Module.Finite R ((K.total c).homology n) := by
  have := finite_total_concrete K n hfinite
  exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv (ConcreteHomology.iso (K.total c) n)).symm

end E2Leading

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneStepFunctions
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

section PlaneArrangementGerms

open Classical

theorem planeSector_open (a : ℕ) (z v : ℝ × ℝ) : IsOpen (planeSector a z v) := by
  have he : planeSector a z v = ⋂ j : Fin 4,
      {p | if cutForm a j v < 0 then cutForm a j p < cutForm a j z
        else cutForm a j z < cutForm a j p} := by ext; simp [planeSector]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  split_ifs
  · exact isOpen_lt (cutForm_continuous a j) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a j)

theorem planeGerm_congr_direction {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v w : ℝ × ℝ} (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (hvw : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    planeGerm f z v=planeGerm f z w := by
  apply planeGerm_eq hv
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z w hw
  refine ⟨N,hN,hz,fun p hp hpv => hf p hp ?_⟩
  intro j
  have hh := hpv j
  simpa only [hvw j] using hh

end PlaneArrangementGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PlaneCornerInjectivity
open Classical

theorem genericPlane_transverse {a : ℕ} (p : GenericPlane a) :
    TransverseDirection a p.val := by
  intro j hj
  exact p.property j 0 (by simpa using hj)

theorem planeGerm_evaluate_incident {a : ℕ} (f : PlaneStep a) {S : Finset PlaneCut}
    (hS : ∀ p q, (∀ l∈S, planeSign l p=planeSign l q) → f.val p=f.val q)
    {z v : ℝ × ℝ} (hv : TransverseDirection a v) {p : GenericPlane a}
    (hp : p.val∈arrangementNeighborhood a S z)
    (hpv : ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
      (cutForm a l.1 p.val<ordinary l.2 ↔ cutForm a l.1 v<0)) :
    f.val p=planeGerm f z v := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨q,hq,hqv⟩ := planeSector_generic hv
    ((arrangementNeighborhood_open a S z).inter hN)
    ⟨self_mem_arrangementNeighborhood a S z,hz⟩
  have hpq : f.val p=f.val q := hS p q (by
    intro l hl
    rw [planeSign_neighborhood hq.1 hqv hl]
    unfold planeSign
    apply decide_eq_decide.mpr
    by_cases he : cutForm a l.1 z=ordinary l.2
    · rw [ite_eq_left he]
      exact hpv l hl he
    · rw [ite_eq_right he]
      have hh := Set.mem_iInter₂.mp hp l hl
      rw [ite_eq_right he] at hh
      by_cases ht : cutForm a l.1 z<ordinary l.2
      · rw [ite_eq_left ht] at hh
        exact iff_of_true hh ht
      · rw [ite_eq_right ht] at hh
        exact iff_of_false (not_lt_of_gt hh) ht)
  exact hpq.trans (hf q hq.2 hqv)

theorem exists_incident_direction {a : ℕ} (S : Finset PlaneCut) (z : ℝ × ℝ)
    (p : GenericPlane a) : ∃ v : ℝ × ℝ, TransverseDirection a v ∧
      ∀ l∈S, cutForm a l.1 z=ordinary l.2 →
        (cutForm a l.1 p.val<ordinary l.2 ↔ cutForm a l.1 v<0) := by
  let U : Set (ℝ × ℝ) := ⋂ l∈S, if cutForm a l.1 z=ordinary l.2 then
    if cutForm a l.1 p.val<ordinary l.2 then {v | cutForm a l.1 v<0}
      else {v | 0 < cutForm a l.1 v} else Set.univ
  have hU : IsOpen U := by
    apply isOpen_biInter_finset
    intro l hl
    split_ifs
    · exact isOpen_lt (cutForm_continuous a l.1) continuous_const
    · exact isOpen_lt continuous_const (cutForm_continuous a l.1)
    · exact isOpen_univ
  have hpU : p.val-z∈U := by
    apply Set.mem_iInter₂.mpr
    intro l hl
    split_ifs with he ht
    · change cutForm a l.1 (p.val-z)<0
      rw [cutForm_sub,he]
      linarith
    · change 0 < cutForm a l.1 (p.val-z)
      rw [cutForm_sub,he]
      have hh := p.property l.1 l.2
      exact sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm hh))
    · trivial
  obtain ⟨v,hv,hvg⟩ := (avoidsCuts_dense a).inter_open_nonempty U hU ⟨p.val-z,hpU⟩
  refine ⟨v,genericPlane_transverse ⟨v,hvg⟩,fun l hl he => ?_⟩
  have hh := Set.mem_iInter₂.mp hv l hl
  rw [ite_eq_left he] at hh
  by_cases ht : cutForm a l.1 p.val<ordinary l.2
  · rw [ite_eq_left ht] at hh
    exact iff_of_true ht hh
  · rw [ite_eq_right ht] at hh
    exact iff_of_false ht (not_lt_of_gt hh)

theorem planeGerm_zero_neighborhood {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    (h : ∀ v, TransverseDirection a v → planeGerm f z v=0) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z∈N ∧
      ∀ p : GenericPlane a, p.val∈N → f.val p=0 := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  refine ⟨arrangementNeighborhood a S z,arrangementNeighborhood_open a S z,
    self_mem_arrangementNeighborhood a S z,fun p hp => ?_⟩
  obtain ⟨v,hv,hpv⟩ := exists_incident_direction S z p
  exact (planeGerm_evaluate_incident f hS hv hp hpv).trans (h v hv)

theorem planeHeight_continuous : Continuous planeHeight := continuous_fst.add continuous_snd

theorem planeSector_generic_descending {a : ℕ} {z v : ℝ × ℝ}
    (hv : TransverseDirection a v) (hdesc : planeHeight v<0)
    {N : Set (ℝ × ℝ)} (hN : IsOpen N) (hz : z∈N) :
    ∃ p : GenericPlane a, p.val∈N ∧ p.val∈planeSector a z v ∧
      planeHeight p.val<planeHeight z := by
  let ray : ℝ → ℝ × ℝ := fun t => z+t • v
  have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
  have he : ray ⁻¹' N∈nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    simpa [ray] using hN.mem_nhds hz
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htN : ray t∈N := hεN (by
    change dist t 0<ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hsector : ray t∈planeSector a z v := by
    intro j
    simp only [ray,cutForm_add,cutForm_smul]
    split_ifs with hj
    · nlinarith
    · have hh := lt_of_le_of_ne (le_of_not_gt hj) (hv j).symm
      nlinarith
  have hdown : planeHeight (ray t)<planeHeight z := by
    change z.1+t*v.1+(z.2+t*v.2)<z.1+z.2
    change v.1+v.2<0 at hdesc
    nlinarith
  obtain ⟨p,hp,hpg⟩ := (avoidsCuts_dense a).inter_open_nonempty
    (N∩planeSector a z v∩{q | planeHeight q<planeHeight z})
    ((hN.inter (planeSector_open a z v)).inter
      (isOpen_lt planeHeight_continuous continuous_const))
    ⟨ray t,⟨htN,hsector⟩,hdown⟩
  exact ⟨⟨p,hpg⟩,hp.1.1,hp.1.2,hp.2⟩

theorem transverse_negative_perturbation {a : ℕ} {v : ℝ × ℝ}
    (hv : TransverseDirection a v) (hh : planeHeight v≤0) :
    ∃ w : ℝ × ℝ, TransverseDirection a w ∧ planeHeight w<0 ∧
      ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0) := by
  let U := planeSector a (0,0) v
  have hvU : v∈U := by
    intro j
    simp only [cutForm_zero]
    split_ifs with hj
    · exact hj
    · exact lt_of_le_of_ne (le_of_not_gt hj) (hv j).symm
  let ray : ℝ → ℝ × ℝ := fun t => v-t • (1,1)
  have hray : Continuous ray := continuous_const.sub (continuous_id.smul continuous_const)
  have he : ray ⁻¹' U∈nhds (0:ℝ) := by
    apply hray.continuousAt.preimage_mem_nhds
    have hz : ray 0=v := by ext <;> simp [ray]
    rw [hz]
    exact (planeSector_open a (0,0) v).mem_nhds hvU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp he
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  have htU : ray t∈U := hεU (by
    change dist t 0<ε
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]
    dsimp [t]; linarith)
  have hs (j : Fin 4) : (cutForm a j v<0 ↔ cutForm a j (ray t)<0) ∧
      cutForm a j (ray t)≠0 := by
    have hj := htU j
    simp only [cutForm_zero] at hj
    by_cases h : cutForm a j v<0
    · rw [ite_eq_left h] at hj
      exact ⟨iff_of_true h hj,ne_of_lt hj⟩
    · rw [ite_eq_right h] at hj
      exact ⟨iff_of_false h (not_lt_of_gt hj),ne_of_gt hj⟩
  refine ⟨ray t,fun j => (hs j).2,?_,fun j => (hs j).1⟩
  change (v.1-t*1)+(v.2-t*1)<0
  change v.1+v.2≤0 at hh
  linarith

end PlaneCornerInjectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerKernel
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
section PlaneCornerKernel
open Classical

theorem planeSupportClosure_compact {a : ℕ} (f : PlaneStep a) :
    IsCompact (planeSupportClosure f) := by
  obtain ⟨R,hR⟩ := PlaneStep.compactSupport f
  have hcompact : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  rintro _ ⟨p,rfl,hp⟩
  have h : |p.val.1|≤R ∧ |p.val.2|≤R := by
    constructor
    · by_contra! hh
      exact hp (hR p (Or.inl hh))
    · by_contra! hh
      exact hp (hR p (Or.inr hh))
  exact ⟨abs_le.mp h.1,abs_le.mp h.2⟩

theorem planeSupportClosure_nonempty {a : ℕ} {f : PlaneStep a} (hf : f≠0) :
    (planeSupportClosure f).Nonempty := by
  have hh : ∃ p : GenericPlane a, f.val p≠0 := by
    by_contra! h
    apply hf
    apply Subtype.ext
    funext p
    exact h p
  obtain ⟨p,hp⟩ := hh
  exact ⟨p.val,subset_closure ⟨p,rfl,hp⟩⟩

theorem planeGerm_zero_at_minimum {a : ℕ} (f : PlaneStep a) {z v : ℝ × ℝ}
    (hmin : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val)
    (hv : TransverseDirection a v) (hdesc : planeHeight v<0) :
    planeGerm f z v=0 := by
  obtain ⟨N,hN,hz,hf⟩ := planeGerm_spec f z v hv
  obtain ⟨p,hp,hpv,hdown⟩ := planeSector_generic_descending hv hdesc hN hz
  by_contra hh
  have hp' : f.val p≠0 := by rwa [hf p hp hpv]
  exact (not_lt_of_ge (hmin p hp')) hdown

theorem planeGerm_zero_at_minimum_le {a : ℕ} (f : PlaneStep a) {z v : ℝ × ℝ}
    (hmin : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val)
    (hv : TransverseDirection a v) (hdesc : planeHeight v≤0) :
    planeGerm f z v=0 := by
  obtain ⟨w,hw,hdown,hvw⟩ := transverse_negative_perturbation hv hdesc
  exact (planeGerm_congr_direction f z hv hw hvw).trans
    (planeGerm_zero_at_minimum f hmin hw hdown)

theorem planeCornerValue_injective_zero {a : ℕ} (f : PlaneStep a)
    (hc : ∀ z v, TransverseDirection a v → planeCornerValue f z v=0) : f=0 := by
  by_contra hf
  obtain ⟨z,hz,hmin⟩ := (planeSupportClosure_compact f).exists_isMinOn
    (planeSupportClosure_nonempty hf) planeHeight_continuous.continuousOn
  have hminimum : ∀ p : GenericPlane a, f.val p≠0 → planeHeight z≤planeHeight p.val := by
    intro p hp
    exact hmin (subset_closure ⟨p,rfl,hp⟩)
  have hbase : planePairValue f z (-1,1)=0 := by
    unfold planePairValue
    rw [planeGerm_zero_at_minimum_le f hminimum (plane_antidiagonal_transverse a)
      (by norm_num [planeHeight])]
    rw [planeGerm_zero_at_minimum_le f hminimum (plane_antidiagonal_transverse a).neg
      (by norm_num [planeHeight])]
    simp
  have hzero : ∀ v, TransverseDirection a v → planeGerm f z v=0 := by
    intro v hv
    have he := hc z v hv
    unfold planeCornerValue at he
    rw [hbase,sub_zero] at he
    change planeGerm f z v+planeGerm f z (-v)=0 at he
    by_cases hh : planeHeight v≤0
    · exact planeGerm_zero_at_minimum_le f hminimum hv hh
    · have hn : planeHeight (-v)≤0 := by
        change -v.1+-v.2≤0
        change ¬v.1+v.2≤0 at hh
        linarith
      rw [planeGerm_zero_at_minimum_le f hminimum hv.neg hn,add_zero] at he
      exact he
  obtain ⟨N,hN,hzN,hfN⟩ := planeGerm_zero_neighborhood f z hzero
  obtain ⟨_,hpN,p,rfl,hp⟩ := mem_closure_iff.mp hz N hN hzN
  exact hp (hfN p hpN)

end PlaneCornerKernel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PlaneCornerCoordinates
open Classical

theorem planeDirectionRep_sign {a : ℕ} {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    planeDirectionSign a (planeDirectionRep a (planeDirectionSign a v))=planeDirectionSign a v := by
  have he : ∃ w, TransverseDirection a w ∧ planeDirectionSign a w=planeDirectionSign a v :=
    ⟨v,hv,rfl⟩
  rw [planeDirectionRep,dite_eq_left he]
  exact (Classical.choose_spec he).2

theorem transverse_neg_sign_congr {a : ℕ} {v w : ℝ × ℝ}
    (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (he : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    ∀ j, (cutForm a j (-v)<0 ↔ cutForm a j (-w)<0) := by
  intro j
  simp only [cutForm_neg,neg_lt_zero]
  constructor <;> intro h
  · by_contra! hh
    have ht := (he j).mpr (lt_of_le_of_ne hh (hw j))
    linarith
  · by_contra! hh
    have ht := (he j).mp (lt_of_le_of_ne hh (hv j))
    linarith

theorem planeCornerValue_congr_direction {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v w : ℝ × ℝ} (hv : TransverseDirection a v) (hw : TransverseDirection a w)
    (he : ∀ j, (cutForm a j v<0 ↔ cutForm a j w<0)) :
    planeCornerValue f z v=planeCornerValue f z w := by
  unfold planeCornerValue planePairValue
  rw [planeGerm_congr_direction f z hv hw he,
    planeGerm_congr_direction f z hv.neg hw.neg (transverse_neg_sign_congr hv hw he)]

theorem planeCornerValue_rep {a : ℕ} (f : PlaneStep a) (z : ℝ × ℝ)
    {v : ℝ × ℝ} (hv : TransverseDirection a v) :
    planeCornerValue f z (planeDirectionRep a (planeDirectionSign a v))=planeCornerValue f z v := by
  apply planeCornerValue_congr_direction f z (planeDirectionRep_transverse _ _) hv
  intro j
  exact decide_eq_decide.mp (congrFun (planeDirectionRep_sign hv) j)

theorem planeCornerCoordinates_injective_zero {a : ℕ} (ha : 0<a) (f : PlaneStep a)
    (hc : ∀ t, planeCornerCoordinates ha f t=0) : f=0 := by
  obtain ⟨S,hS⟩ := PlaneStep.hasArrangement f
  apply planeCornerValue_injective_zero f
  intro z v hv
  by_contra hn
  obtain ⟨l,hl,k,hk,hdir,hzl,hzk⟩ := planeCornerValue_exists_incident f hS hv hn
  obtain ⟨t,x,y,hz⟩ := all_intersections_finite_templates ha l.1 k.1 hdir l.2 k.2 z hzl hzk
  have he := congrArg (fun q : PolygonGroupRing => q.coeff (Multiplicative.ofAdd (x,y)))
    (hc (t,planeDirectionSign a v))
  change planeCornerValue f (planeVertexPosition a t (Multiplicative.ofAdd (x,y)))
    (planeDirectionRep a (planeDirectionSign a v))=0 at he
  rw [planeCornerValue_rep f _ hv] at he
  exact hn (hz ▸ he)

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonCoefficientFinite
open Classical

theorem planeCornerEmbedding_injective {a : ℕ} (ha : 0<a) :
    Function.Injective (planeCornerEmbedding ha) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply (PlaneStep.representation a).asModuleEquiv.injective
  apply planeCornerCoordinates_injective_zero ha
  intro t
  exact congrFun hf t

theorem polygon_coefficient_finite {a : ℕ} (ha : 0<a) :
    Module.Finite PolygonGroupRing (PlaneStep.representation a).asModule :=
  Module.Finite.of_injective (planeCornerEmbedding ha) (planeCornerEmbedding_injective ha)

end PolygonCoefficientFinite

section NoetherianResolution
open _root_.CategoryTheory CategoryTheory.Limits
universe nr

namespace NoetherianResolution
variable {R : Type nr} [CommRing R] [IsNoetherianRing R]

theorem finite_short_homology (S : ShortComplex (ModuleCat.{nr} R))
    [Module.Finite R S.X₂] : Module.Finite R S.homology := by
  have : Module.Finite R (LinearMap.ker S.g.hom) :=
    Module.Finite.of_injective (LinearMap.ker S.g.hom).subtype Subtype.val_injective
  have : Module.Finite R S.moduleCatLeftHomologyData.H := by
    exact Module.Finite.of_surjective (LinearMap.range S.moduleCatToCycles).mkQ
      (LinearMap.range S.moduleCatToCycles).mkQ_surjective
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.inv.hom
    S.moduleCatHomologyIso.toLinearEquiv.symm.surjective

theorem finite_homology (C : ChainComplex (ModuleCat.{nr} R) ℕ) (n : ℕ)
    [Module.Finite R (C.X n)] : Module.Finite R (C.homology n) := by
  have : Module.Finite R (C.sc n).X₂ := ‹Module.Finite R (C.X n)›
  exact finite_short_homology (C.sc n)

end NoetherianResolution
end NoetherianResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_NoetherianTor
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
section NoetherianTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe nt

namespace NoetherianResolution
variable {R : Type nt} [CommRing R]

theorem homologyMap_smul {C D : ChainComplex (ModuleCat.{nt} R) ℕ}
    (f : C ⟶ D) (r : R) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n =
      r • HomologicalComplex.homologyMap f n := by
  exact ShortComplex.homologyMap_smul
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) _ n).map f) r

theorem annihilator_homology {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (F : ModuleCat.{nt} R ⥤ ModuleCat.{nt} R)
    [F.Additive] [Functor.Linear R F] (r : R) (hr : ∀ x : M, r • x = 0)
    (n : ℕ) (x : ((F.mapHomologicalComplex _).obj P.complex).homology n) :
    r • x = 0 := by
  have h := (F.mapHomotopy (annihilatorHomotopy P r hr)).homologyMap_eq n
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero,
    homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

variable [IsNoetherianRing R]

theorem finite_tensor_resolution_homology (L M : FGModuleCat.{nt} R) (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).homology n) := by
  have : Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).X n) :=
    Module.Finite.tensorProduct R L ((resolution M).complex.X n)
  exact finite_homology _ n

end NoetherianResolution

theorem module_finite_int_of_augmentation {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ε : R →+* ℤ) (h : ∀ (r : R) (x : M), r • x = ε r • x) :
    Module.Finite ℤ M := by
  obtain ⟨s,hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [h]; exact Submodule.smul_mem _ _ hx

end NoetherianTor

section AugmentationTor
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace NoetherianResolution
variable {R : Type} [CommRing R] [IsNoetherianRing R]

instance finite_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite R ((augmentationComplex ε L).homology n) :=
  finite_tensor_resolution_homology L (FGModuleCat.of R (augmentationModule ε)) n

theorem augmentation_homology_smul (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ)
    (r : R) (x : (augmentationComplex ε L).homology n) :
    r • x = ε r • x := by
  have h0 : ∀ z : augmentationModule ε, (r - (ε r : R)) • z = 0 := by
    intro z
    change ε (r - (ε r : R)) • z = 0
    simp only [map_sub, map_intCast, Int.cast_id, sub_self, zero_smul]
  have h := annihilator_homology (augmentationResolution ε)
    ((tensoringLeft (ModuleCat R)).obj L.obj) (r - (ε r : R)) h0 n x
  have h' : (r - (ε r : R)) • x = 0 := h
  rw [sub_smul, sub_eq_zero] at h'
  simpa only [Int.cast_smul_eq_zsmul] using h'

theorem finite_int_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ ((augmentationComplex ε L).homology n) :=
  module_finite_int_of_augmentation ε (augmentation_homology_smul ε L n)

end NoetherianResolution
end AugmentationTor

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RingGroupHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section RingGroupHomology

open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

variable [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology_inverse (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ (groupHomology (inverseRep L.obj) n) := by
  classical
  let C := NoetherianResolution.augmentationComplex (augmentation (G := G)) L
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let := NoetherianResolution.finite_int_augmentation_homology augmentation L n
  let e0 : ModuleCat.of ℤ (C.homology n) ≅ F.obj (C.homology n) := intRestrictionIso _
  have : Module.Finite ℤ (F.obj (C.homology n)) :=
    Module.Finite.of_surjective e0.hom.hom e0.toLinearEquiv.surjective
  let e1 : ((F.mapHomologicalComplex _).obj C).homology n ≅
      F.obj (C.homology n) := (C.sc n).mapHomologyIso F
  have : Module.Finite ℤ (((F.mapHomologicalComplex _).obj C).homology n) :=
    Module.Finite.of_surjective e1.inv.hom e1.toLinearEquiv.symm.surjective
  let e2 := HomologicalComplex.homologyMapIso (complexIso L) n
  have : Module.Finite ℤ (((groupResolution (G := G)).complex.coinvariantsTensorObj
      (inverseRep L.obj)).homology n) :=
    Module.Finite.of_surjective e2.inv.hom e2.toLinearEquiv.symm.surjective
  let e3 := groupHomologyIso (inverseRep L.obj) n (groupResolution (G := G))
  exact Module.Finite.of_surjective e3.inv.hom e3.toLinearEquiv.symm.surjective

end RingCoinvariants
end RingGroupHomology

section FiniteAbelianHomology

open _root_.CategoryTheory
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G] [IsNoetherianRing (MonoidAlgebra ℤ G)]

theorem finite_groupHomology (A : Rep ℤ G)
    [Module.Finite (MonoidAlgebra ℤ G) A.ρ.asModule] (n : ℕ) :
    Module.Finite ℤ (groupHomology A n) := by
  let L := FGModuleCat.of (MonoidAlgebra ℤ G) A.ρ.asModule
  have := finite_groupHomology_inverse L n
  let e := inverseHomologyIso A n
  exact Module.Finite.of_surjective e.hom.hom e.toLinearEquiv.surjective

end RingCoinvariants
end FiniteAbelianHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlanePeriodization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PlanePeriodization

open Classical
namespace SquareStep
variable {a : ℕ}

theorem slice_extend (f : SquareStep a) (n : ℤ×ℤ) (hn : n≠0) :
    slice n (extend f)=0 := by
  apply Subtype.ext
  funext p
  rw [slice_apply,extend_apply]
  apply dite_eq_right
  intro h
  have h' : (0 ≤ p.val.1+(n.1:ℝ) ∧ p.val.1+(n.1:ℝ)<1) ∧
      (0 ≤ p.val.2+(n.2:ℝ) ∧ p.val.2+(n.2:ℝ)<1) := by
    simpa [InSquare,GenericPlane.shift,intPair] using h
  have hx : (-1:ℤ)<n.1 ∧ n.1<1 := by
    have hr : (-1:ℝ)<(n.1:ℝ) ∧ (n.1:ℝ)<1 :=
      ⟨by linarith [p.property.1.2,h'.1.1],by linarith [p.property.1.1,h'.1.2]⟩
    exact_mod_cast hr
  have hy : (-1:ℤ)<n.2 ∧ n.2<1 := by
    have hr : (-1:ℝ)<(n.2:ℝ) ∧ (n.2:ℝ)<1 :=
      ⟨by linarith [p.property.2.1.2,h'.2.1],by linarith [p.property.2.1.1,h'.2.2]⟩
    exact_mod_cast hr
  exact hn (Prod.ext (by dsimp; omega) (by dsimp; omega))

@[simp] theorem periodize_extend (f : SquareStep a) : periodize (extend f)=f := by
  change (∑ᶠ n : ℤ×ℤ, slice n (extend f))=f
  rw [finsum_eq_single _ 0 (fun n hn => slice_extend f n hn),slice_zero,restrict_extend]

theorem periodize_surjective : Function.Surjective (periodize (a := a)) :=
  fun f => ⟨extend f,periodize_extend f⟩

end SquareStep
end PlanePeriodization

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TorusCoefficientFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.translationEvaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.emptyPointIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.pointEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.TranslationFiltered.regular_filtered
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
section TorusCoefficientFinite

open Classical
namespace SquareStep

theorem periodizeModule_surjective {a : ℕ} :
    Function.Surjective (periodizeModule (a := a)) := periodize_surjective

theorem orbit_coefficient_finite {a : ℕ} (ha : 0<a) :
    Module.Finite OrbitGroupRing (orbitRepresentation a).asModule := by
  let := polygon_coefficient_finite ha
  exact Module.Finite.of_surjective periodizeModule periodizeModule_surjective

end SquareStep
end TorusCoefficientFinite

section TensorCoefficientFinite

open scoped TensorProduct
attribute [local instance 1200] Representation.instModuleAsModule TensorProduct.instModule
attribute [local instance 1300] TensorProduct.leftModule
namespace RingCoinvariants

theorem finite_tensor (k R M K : Type*) [CommRing k] [CommRing R] [Algebra k R]
    [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
    [SMulCommClass k R M] [AddCommGroup K] [Module k K]
    [Module.Finite R M] [Module.Finite k K] : Module.Finite R (M ⊗[k] K) := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange k R R M K
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

variable {G M K : Type} [CommGroup G] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup K] [Module ℤ K]
local notation "R" => MonoidAlgebra ℤ G

theorem finite_trivialTensor (ρ : Representation ℤ G M)
    [Module.Finite R ρ.asModule] [Module.Finite ℤ K] :
    Module.Finite R (ρ.tprod (Representation.trivial ℤ G K)).asModule := by
  let : Module.Finite R (ρ.asModule ⊗[ℤ] K) := finite_tensor ℤ R ρ.asModule K
  exact Module.Finite.of_surjective (trivialTensorMap ρ) (trivialTensorEquiv ρ).surjective

end RingCoinvariants
end TensorCoefficientFinite

section PolygonCoefficientHomology

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
namespace SquareStep

theorem coefficient_homology_finite {a : ℕ} (ha : 0<a) (K : Type)
    [AddCommGroup K] [Module ℤ K] [Module.Finite ℤ K] (n : ℕ) :
    Module.Finite ℤ (groupHomology (coefficientRep a K) n) := by
  let : Module.Finite OrbitGroupRing (orbitRepresentation a).asModule :=
    orbit_coefficient_finite ha
  let : Module.Finite OrbitGroupRing (coefficientRep a K).ρ.asModule :=
    RingCoinvariants.finite_trivialTensor (orbitRepresentation a)
  exact RingCoinvariants.finite_groupHomology (coefficientRep a K) n

end SquareStep
end PolygonCoefficientHomology

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalFiniteness
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalFiniteness

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)

lemma finite [IsNoetherianRing R] (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite R ((row K q).homology p)) :
    Module.Finite R ((K.total c).homology n) := by
  apply E2Leading.finite_total K n
  intro p q hpq
  have := hfinite p q hpq
  exact Module.Finite.equiv (rowHomologyIso K p q).toLinearEquiv

end TotalFiniteness

namespace EilenbergZilber
open DiagonalResolution ModelAssembly
variable (X : Dᵒᵖ ⥤ Type)

lemma finite_diagonal (n : ℕ)
    (hfinite : ∀ p q, p+q=n → Module.Finite ℤ
      ((TotalFiniteness.row (twoComplex X) q).homology p)) :
    Module.Finite ℤ (SSet.homology (C := A) (diag ⋙ X) Z n) := by
  have := TotalFiniteness.finite (twoComplex X) n hfinite
  exact Module.Finite.equiv (homologyIso X n).symm.toLinearEquiv

end EilenbergZilber

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialH0
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

lemma finite_homology (K : ChainComplex A ℕ) (n : ℕ) [Module.Finite ℤ (K.X n)] :
    Module.Finite ℤ (K.homology n) := by
  have : Module.Finite ℤ (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end BarHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ResolutionAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]

lemma constantMap_verticalAugmentation :
    SimplicialDiagonal.nerveDiagonal.map (constantMap W) ≫ verticalAugmentation W =
      (constantDiagonalIso (C:=C)).hom := by
  ext n F
  refine CategoryTheory.Functor.ext (fun _=>rfl) ?_
  intro i j f
  erw [Category.id_comp, Category.comp_id]
  change F.map f ≫ 𝟙 _ = F.map f
  simp
  all_goals exact Category.comp_id _

lemma resolutionAugmentation_homology (j:ℕ) :
    SSet.homologyMap (resolutionAugmentation W) DiagonalResolution.Z j = (homologyIso W j).hom := by
  let H := SSet.homologyFunctor DiagonalResolution.Z j
  let N := SimplicialDiagonal.nerveDiagonal
  have constantMap_isIso : IsIso (H.map (N.map (constantMap W))) :=
    SimplicialDiagonal.nerveDiagonal_isIso (constantMap W)
      (fun p=>inferInstanceAs (constant W p.unop.len).IsEquivalence) j
  have hc := congrArg H.map (constantMap_verticalAugmentation W)
  simp only [Functor.map_comp] at hc
  have hv : H.map (verticalAugmentation W) = inv (H.map (N.map (constantMap W))) ≫
      H.map (constantDiagonalIso (C:=C)).hom := by
    rw [←hc,←Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  change H.map ((diagonalIso W).hom ≫ verticalAugmentation W) =
    H.map (diagonalIso W).hom ≫ inv (H.map (N.map (constantMap W))) ≫ H.map (constantDiagonalIso (C:=C)).hom
  rw [Functor.map_comp,hv]
noncomputable instance resolutionAugmentation_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (resolutionAugmentation W) DiagonalResolution.Z j) := by
  rw [resolutionAugmentation_homology]
  infer_instance
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]

lemma tripleResolutionAugmentation_homology (p q r j:ℕ) :
    SSet.homologyMap (tripleResolutionAugmentation W p q r) DiagonalResolution.Z j =
      (tripleDiagramResolutionHomologyIso W p q r j).hom := by
  change (SSet.homologyFunctor DiagonalResolution.Z j).map
      (SimplicialDiagonal.nerveDiagonal.map (tripleDiagramTranspose W p q r) ≫
        resolutionAugmentation (property₃ W p q r) ≫ nerveMap (triplePosInclusion W p q r)) = _
  simp only [Functor.map_comp]
  rw [show (SSet.homologyFunctor DiagonalResolution.Z j).map (resolutionAugmentation (property₃ W p q r)) =
    (homologyIso (property₃ W p q r) j).hom from resolutionAugmentation_homology _ j]
  rfl
noncomputable instance tripleResolutionAugmentation_isIso (p q r j:ℕ) :
    IsIso (SSet.homologyMap (tripleResolutionAugmentation W p q r) DiagonalResolution.Z j) := by
  rw [tripleResolutionAugmentation_homology]
  infer_instance
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_Supplemental
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

section
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance innerResolutionTotal_isIso (q r j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (innerResolutionAugmentation W q r))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact tripleResolutionAugmentation_isIso W p.unop.len q r n

noncomputable instance middleResolutionTotal_isIso (r j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (middleResolutionAugmentation W r))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact innerResolutionTotal_isIso W p.unop.len r n

noncomputable instance tripleResolutionTotal_isIso (j:ℕ) :
    IsIso (SSet.homologyMap
      (SimplicialDiagonal.diagonal.map (outerResolutionAugmentation W))
      DiagonalResolution.Z j) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p n
  exact middleResolutionTotal_isIso W p.unop.len n
end

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [W.IsStableUnderBraiding]
noncomputable instance totalStringToBar_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (totalStringToBar W) DiagonalResolution.Z j) := by
  unfold totalStringToBar
  rw [SSet.homologyMap_comp]
  have := tripleResolutionTotal_isIso W j
  infer_instance
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StringBarNaturality
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimplicialDiagonal.diagonal_preserves _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance stringBarAugmentation_isIso (j:ℕ) :
    IsIso (SSet.homologyMap (stringBarAugmentation W) DiagonalResolution.Z j) := by
  unfold stringBarAugmentation
  rw [SSet.homologyMap_comp]
  have totalAugmentationIso := totalStringToBar_isIso W j
  infer_instance
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryFinite
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_essSurj _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_faithful _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_full _root_.OAI.SimpleAmenable.PolygonTracks.standardFiberInclusion_isEquivalence _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Opposite AlgebraicTopology HomologicalComplex
namespace SimplicialDiagonal

lemma rows_connected (X : I ⥤ SSet) (hX : ∀ n,SSet.IsConnected (X.obj n)) (p : I) :
    SSet.IsConnected ((EilenbergZilber.bisimplicial (uncurry X)).obj p) := by
  have := hX p
  exact BarFinitePower.connected_of_iso _ (rowIso X p)
end SimplicialDiagonal
namespace BarHomology
open FreeChains

lemma zeroRow_finite (X : DiagonalResolution.Dᵒᵖ ⥤ Type)
    (hc : ∀ p, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj p)) (p : ℕ) :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p) := by
  let K := AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj Z)
  have : Module.Finite ℤ (K.X p) := by
    change Module.Finite ℤ (ModuleCat.of ℤ ℤ)
    infer_instance
  have : Module.Finite ℤ (K.homology p) := finite_homology K p
  let e : K.homology p ≅ (TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p :=
    (homologyFunctor A c p).mapIso (zeroRowIso X hc).symm
  exact Module.Finite.equiv e.toLinearEquiv
end BarHomology
namespace RestrictedNerve
open IntervalBar.Diagram
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma stringBarRows_connected (p : SimplexCategoryᵒᵖ) : SSet.IsConnected ((stringBarRows W).obj p) :=
  bar₃_connected
lemma finite_bar₃_of_string (n : ℕ)
    [Module.Finite ℤ (SSet.homology (C:=FreeChains.A) (SimplicialDiagonal.diagonal.obj (stringBarRows W)) DiagonalResolution.Z n)] :
    Module.Finite ℤ ((bar₃ (C:=C)).homology DiagonalResolution.Z n : FreeChains.A) :=
  Module.Finite.equiv (asIso (SSet.homologyMap (stringBarAugmentation W) DiagonalResolution.Z n)).toLinearEquiv
end RestrictedNerve
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
lemma trajectoryE2_finite (a p q : ℕ) (ha : 0<a) (hq : 0<q) (hq5 : q≤5)
    [Module.Finite ℤ (Stage.K q)] :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex
      (SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a)))) q).homology p) := by
  have he : trajectoryRep a q = SquareStep.coefficientRep a (Stage.K q) := by
    unfold trajectoryRep
    congr 1
    exact Subsingleton.elim _ _
  have : Module.Finite ℤ (groupHomology (trajectoryRep a q) p) := by
    rw [he]
    exact SquareStep.coefficient_homology_finite ha (Stage.K q) p
  exact Module.Finite.equiv (trajectoryE2Iso a p q hq hq5).symm.toLinearEquiv
lemma polygon_bar₃_finite_of_symmetric (a : ℕ) (ha : 0<a)
    (hK : ∀ q, 0<q → q≤5 → Module.Finite ℤ (Stage.K q)) (n : ℕ) (hn : n≤5) :
    Module.Finite ℤ ((bar₃ (C:=PolygonObject a)).homology Z n : A) := by
  let X := SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a))
  have hc : ∀ p, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj p) :=
    SimplicialDiagonal.rows_connected _ (RestrictedNerve.stringBarRows_connected _)
  have : Module.Finite ℤ (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n) := by
    apply EilenbergZilber.finite_diagonal X n
    intro p q hpq
    by_cases hq : q=0
    · subst q
      exact BarHomology.zeroRow_finite X hc p
    · have := hK q (by omega) (by omega)
      exact trajectoryE2_finite a p q ha (by omega) (by omega)
  have : Module.Finite ℤ (SSet.homology (C:=A)
      (SimplicialDiagonal.diagonal.obj (RestrictedNerve.stringBarRows (positionalProperty a)))
      DiagonalResolution.Z n) := ‹Module.Finite ℤ (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n)›
  exact RestrictedNerve.finite_bar₃_of_string (positionalProperty a) n
end SimpleAmenable.PolygonObject.LabelledStage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable
open FreeChains IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2

lemma polygon_triple_homology_finite (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤5) :
    Module.Finite ℤ ((bar₃ (C:=PolygonObject a)).homology Z n:A) := by
  apply PolygonObject.LabelledStage.polygon_bar₃_finite_of_symmetric a ha _ n hn
  intro q _ hq
  exact SymmetricConfiguration.triple_homology_finite q hq

lemma polygon_bar_homology_finite_oai (a:ℕ) (ha:0<a) (n:ℕ) (hn:n≤3) :
    Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z n:A) :=
  bar_finite_of_triple (polygon_triple_homology_finite a ha) n hn

end SimpleAmenable

end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.polygon_bar_homology_finite_oai := @OAI.SimpleAmenable.polygon_bar_homology_finite_oai
