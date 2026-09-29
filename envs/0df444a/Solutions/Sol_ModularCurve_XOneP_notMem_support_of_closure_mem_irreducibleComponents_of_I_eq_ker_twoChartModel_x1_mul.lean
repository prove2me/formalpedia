-- Prove2me | solution 1 for ModularCurve.XOneP.notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1686de08-4348-50a3-89ed-04d4a1e3318d

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

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
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hI₁ : ((i₁.1 ≫ bc).ker).IsInvertible) (hI₂ : ((i₂.1 ≫ bc).ker).IsInvertible)
    (hI₁₂ : (i₁.1 ≫ bc).ker * (i₂.1 ≫ bc).ker = bc.ker)

    (htoκs : Function.Surjective toκ)
    (T' : Type) [Field T'] [Algebra O T'] [IsFractionRing O T']
    (hsmT : SmoothOfRelativeDimension 1
      (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO)))))
    (r : ℕ) (E : RelEffCartierDiv (ModularCurve.TwoChart.modelTo A (↥K) j) r (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))))

    (Ebar : RelEffCartierDiv (ModularCurve.TwoChart.modelTo A (↥K) j) r (Spec.map (CommRingCat.ofHom ρO)))
    (hJ : Ebar.I = (E.I.subschemeι ≫ mapOnProdOver (ModularCurve.TwoChart.modelTo A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap O T')))
        (show Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ Spec.map (CommRingCat.ofHom ρO) =
            Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO)) by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])).ker)
    (hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).affineOpens)
        (s : Γ(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)), U)),
        (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).presheaf.map (homOfLE (le_top : (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).Opens) ≤ ⊤)).op
            ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).appTop
              ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈ Ebar.I.ideal U →
          s ∈ Ebar.I.ideal U) :
    (∀ ξ : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), (∀ y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), y ⤳ ξ → y = ξ) →
        bc.base ξ ∉ (Ebar.I.support : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))))) ∧
    (∃ c : ↥C₁, (i₁.1 ≫ bc).base c ∉ (Ebar.I.support : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))))) ∧
    (∃ c : ↥C₂, (i₂.1 ≫ bc).base c ∉ (Ebar.I.support : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))))) := by
  classical
  haveI : IsIntegral C₁ := AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral c₁
  haveI : IsIntegral C₂ := AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral c₂

  have hφ : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) = specMap A k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκ]
  have hbc : bc = mapOnProdOver (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom toκ)) hφ := by
    apply pullback.hom_ext
    · rw [hbc₁, mapOnProdOver_fst]
    · rw [hbc₂, mapOnProdOver_snd]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom toκ)) :=
    IsClosedImmersion.spec_of_surjective _ htoκs
  haveI hbcCI : IsClosedImmersion bc := by
    rw [hbc]
    exact MorphismProperty.of_isPullback
      (isPullback_mapOnProdOver (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom toκ)) hφ).flip
      inferInstance

  haveI := Ebar.isFinite

  let t₀ : ↥(Spec (CommRingCat.of k)) := ⟨⊥, Ideal.bot_prime⟩
  let s₀ : ↥(Spec (CommRingCat.of O)) := (Spec.map (CommRingCat.ofHom toκ)).base t₀
  have hsnd : ∀ y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).base (bc.base y) = s₀ := by
    intro y
    have h1 : (bc ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).base y =
        (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ Spec.map (CommRingCat.ofHom toκ)).base y := by
      rw [hbc₂]
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
    rw [h1]
    change (Spec.map (CommRingCat.ofHom toκ)).base _ = (Spec.map (CommRingCat.ofHom toκ)).base t₀
    congr 1
    exact Subsingleton.elim _ _

  have core : ∀ (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
      [IsClosedImmersion i] (c : ↥C) (hc : c ≠ genericPoint ↥C),
      (i ≫ bc).base (genericPoint ↥C) ∉ (Ebar.I.support : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))) := by
    intro C _ i _ c hc hη
    haveI : IsClosedImmersion (i ≫ bc) := inferInstance
    have hηc : genericPoint ↥C ⤳ c := genericPoint_specializes c
    have h1 : (i ≫ bc).base (genericPoint ↥C) ⤳ (i ≫ bc).base c := hηc.map (i ≫ bc).base.hom.continuous
    have hc' : (i ≫ bc).base c ∈ (Ebar.I.support : Set _) := h1.mem_closed Ebar.I.support.isClosed hη
    rw [← Scheme.IdealSheafData.range_subschemeι] at hη hc'
    obtain ⟨e₁, he₁⟩ := hη
    obtain ⟨e₂, he₂⟩ := hc'
    have hsp : e₁ ⤳ e₂ := by
      rw [← Ebar.I.subschemeι.isClosedEmbedding.isInducing.specializes_iff]
      change Ebar.I.subschemeι.base e₁ ⤳ Ebar.I.subschemeι.base e₂
      rw [he₁, he₂]; exact h1

    set q := Ebar.I.subschemeι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)) with hq
    have hq₁ : q.base e₁ = s₀ := by
      rw [hq, Scheme.Hom.comp_base, TopCat.comp_app, he₁, Scheme.Hom.comp_base, TopCat.comp_app]; exact hsnd _
    have hq₂ : q.base e₂ = s₀ := by
      rw [hq, Scheme.Hom.comp_base, TopCat.comp_app, he₂, Scheme.Hom.comp_base, TopCat.comp_app]; exact hsnd _
    have hdisc := q.isDiscrete_preimage_singleton s₀
    have heq : e₁ = e₂ := hdisc.eq_of_specializes hsp (by simpa using hq₁) (by simpa using hq₂)
    have hgeq : (i ≫ bc).base (genericPoint ↥C) = (i ≫ bc).base c := by rw [← he₁, ← he₂, heq]
    exact hc ((i ≫ bc).isClosedEmbedding.injective hgeq).symm

  have hng : ∀ (C : Scheme.{0}) (cC : C ⟶ Spec (CommRingCat.of k)) [IsProper cC] [SmoothOfRelativeDimension 1 cC]
      [GeometricallyIntegral cC] [IsIntegral C], ∃ c : ↥C, c ≠ genericPoint ↥C := by
    intro C cC _ _ _ _
    obtain ⟨-, x, hx⟩ :=
      AlgebraicGeometry.isClosed_singleton_or_isGenericPoint_and_exists_not_isGenericPoint_of_smoothOfRelativeDimension_one k cC
    refine ⟨x, fun h => hx ?_⟩
    rw [h]
    exact genericPoint_spec ↥C
  obtain ⟨c₁', hc₁'⟩ := hng C₁ c₁
  obtain ⟨c₂', hc₂'⟩ := hng C₂ c₂
  have core₁ := core C₁ i₁.1 c₁' hc₁'
  have core₂ := core C₂ i₂.1 c₂' hc₂'
  refine ⟨?_, ⟨genericPoint ↥C₁, core₁⟩, ⟨genericPoint ↥C₂, core₂⟩⟩
  intro ξ hmax
  rcases hcover ξ with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · have hsp : i₁.1.base (genericPoint ↥C₁) ⤳ i₁.1.base z := (genericPoint_specializes z).map i₁.1.base.hom.continuous
    rw [← hmax _ hsp]
    simpa [Scheme.Hom.comp_base] using core₁
  · have hsp : i₂.1.base (genericPoint ↥C₂) ⤳ i₂.1.base z := (genericPoint_specializes z).map i₂.1.base.hom.continuous
    rw [← hmax _ hsp]
    simpa [Scheme.Hom.comp_base] using core₂

end S_ModularCurve_XOneP_notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_notMem_support_of_closure_mem_irreducibleComponents_of_I_eq_ker_twoChartModel_x1_mul (solution)
