-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a9680770-efe2-50b1-b1dc-2421fc463952

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ringEquiv_residueField_functionField_of_isIntegral
import Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

universe u

namespace GenPt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

theorem infinite_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] : Infinite ↥C := by
  haveI := (AlgebraicCurve.infinite_setOf_isClosed_singleton c).to_subtype
  exact Infinite.of_injective (Subtype.val : {x : ↥C | IsClosed ({x} : Set ↥C)} → ↥C) Subtype.val_injective

theorem not_range_subset_range
    {k : Type u} [Field k] {X C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k))
    [IsIntegral C₁] [SmoothOfRelativeDimension 1 c₁]
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X)
    (n : ℕ) (hn : Nat.card ↥(pullback i₁ i₂) = n) (hn0 : 0 < n) :
    ¬ (Set.range i₁.base ⊆ Set.range i₂.base) := by
  intro hsub
  haveI : Finite ↥(pullback i₁ i₂) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
  have hsurj : Function.Surjective (pullback.fst i₁ i₂).base := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    exact fun x => hsub ⟨x, rfl⟩
  haveI : Finite ↥C₁ := Finite.of_surjective _ hsurj
  haveI := infinite_of_smoothOfRelativeDimension_one c₁
  exact not_finite ↥C₁

theorem eq_of_specializes_image_genericPoint
    {k : Type u} [Field k] {X C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k))
    [IsIntegral C₁] [SmoothOfRelativeDimension 1 c₁]
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : ↥X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (n : ℕ) (hn : Nat.card ↥(pullback i₁ i₂) = n) (hn0 : 0 < n)
    (ξ : ↥C₁) (hξ : IsGenericPoint ξ ⊤) (η'' : ↥X) (h : η'' ⤳ i₁.base ξ) : η'' = i₁.base ξ := by
  have hZ1 : closure ({i₁.base ξ} : Set ↥X) = Set.range i₁.base := by
    rw [← Set.image_singleton, i₁.isClosedEmbedding.closure_image_eq, hξ.def, Set.top_eq_univ, Set.image_univ]
  have hirr : IsPreirreducible (closure ({η''} : Set ↥X)) := isPreirreducible_singleton.closure
  have hcov : closure ({η''} : Set ↥X) ⊆ Set.range i₁.base ∪ Set.range i₂.base := fun z _ => hcover z
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr) _ _ i₁.isClosedEmbedding.isClosed_range
      i₂.isClosedEmbedding.isClosed_range hcov with h1 | h2
  ·
    have : i₁.base ξ ⤳ η'' := by
      rw [specializes_iff_mem_closure, hZ1]
      exact h1 (subset_closure rfl)
    exact (this.antisymm h).eq.symm
  ·
    exfalso
    apply not_range_subset_range c₁ i₁ i₂ n hn hn0
    rw [← hZ1]
    have hmem : i₁.base ξ ∈ closure ({η''} : Set ↥X) := specializes_iff_mem_closure.mp h
    exact (closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure).trans h2

end GenPt

set_option maxHeartbeats 12800000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ∀ (F : Type) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C₂),
      e.hom ≫ c₂ = Mdl.toBase →
    ∀ ξ : ↥C₂, IsGenericPoint ξ ⊤ →
      letI : Algebra A ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) :=
        RingHom.toAlgebra (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) trivial).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
      ∃ (𝔮 : Ideal (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ))))
        (_ : 𝔮 ∈ minimalPrimes (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)))),
        Nonempty (F ≃ₐ[k] FractionRing (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ⧸ 𝔮)) := by
  intro F _ _ Mdl e he ξ hξ

  haveI : IsIntegral C₂ := IsIntegral.of_isIso (pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k))))
  obtain rfl : ξ = genericPoint C₂ := hξ.eq (genericPoint_spec C₂)

  obtain ⟨𝔮, h𝔮, ψ, hψ, hmin⟩ :=
    AlgebraicGeometry.exists_ideal_residueField_pullback_algEquiv_fractionRing_tensorProduct_stalk_quotient
      A (ModularCurve.TwoChart.modelTo A (↥K) j) k (i₂.1.base (genericPoint C₂))

  have hn' : Nat.card ↥(pullback i₂.1 i₁.1) = n := by
    rw [← hn]
    exact Nat.card_congr (pullbackSymmetry i₂.1 i₁.1).hom.homeomorph.toEquiv
  have hcover' : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      z ∈ Set.range i₂.1.base ∨ z ∈ Set.range i₁.1.base := fun z => (hcover z).symm
  have hmaxk := GenPt.eq_of_specializes_image_genericPoint c₂ i₂.1 i₁.1 hcover' n hn' hn0 (genericPoint C₂) (genericPoint_spec C₂)
  refine ⟨𝔮, hmin hmaxk, ?_⟩

  letI algF : Algebra k Mdl.C.functionField := (AlgebraicCurve.baseToFunctionField Mdl.toBase).toAlgebra
  letI algC : Algebra k C₂.functionField := (AlgebraicCurve.baseToFunctionField c₂).toAlgebra
  obtain ⟨eMC⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso Mdl.toBase c₂ e he
  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.IsClosedImmersion.exists_ringEquiv_residueField_functionField_of_isIntegral i₂.1

  letI algκ : Algebra k ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residueField
      (i₂.1.base (genericPoint C₂))) :=
    RingHom.toAlgebra (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue
        (i₂.1.base (genericPoint C₂))).hom.comp
      (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤
          (i₂.1.base (genericPoint C₂)) trivial).hom.comp
        (((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)))

  have hθk : ∀ c : k, θ (algebraMap k _ c) = algebraMap k C₂.functionField c := by
    intro c
    show θ (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residue (i₂.1.base (genericPoint C₂))).hom (((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤ (i₂.1.base (genericPoint C₂)) trivial).hom
      (((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)))) =
      (C₂.presheaf.germ ⊤ (genericPoint C₂) trivial).hom (c₂.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    rw [hθ, Scheme.Hom.germ_stalkMap_apply]
    congr 1
    show ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop ≫ i₂.1.appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) = _
    rw [← Scheme.Hom.comp_appTop, i₂.2]
  let θk : ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A k)))).residueField
      (i₂.1.base (genericPoint C₂))) ≃ₐ[k] C₂.functionField :=
    AlgEquiv.ofRingEquiv (f := θ) hθk
  exact ⟨(Mdl.ffAlgEquiv.trans eMC).trans (θk.symm.trans ψ)⟩

#print axioms solution

end S_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul (solution)
