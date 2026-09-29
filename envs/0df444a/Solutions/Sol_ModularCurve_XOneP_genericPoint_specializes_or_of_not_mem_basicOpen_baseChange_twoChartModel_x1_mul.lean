-- Prove2me | solution 1 for ModularCurve.XOneP.genericPoint_specializes_or_of_not_mem_basicOpen_baseChange_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e91bd0c7-70bd-554b-bcf7-e3b44aa97631

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_genericPoint_specializes_or_of_not_mem_basicOpen_baseChange_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

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
    (ρO : A →+* O) (hρO : Function.Injective ρO) (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    [IsIntegral C₁] [IsIntegral C₂]
    (y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))))
    (hy : (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).base y ∉
      (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens)) :
    (i₁.1 ≫ bc).base (genericPoint C₁) ⤳ y ∨ (i₂.1 ≫ bc).base (genericPoint C₂) ⤳ y := by
  classical

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    have hpA : ((p : ℕ) : A) ≠ 0 := by
      intro h
      have h' := congrArg (algebraMap A L) h
      rw [map_natCast, map_zero] at h'
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
    have hpO : ρO ((p : ℕ) : A) ≠ 0 := fun h => hpA (hρO (by rw [h, map_zero]))
    have hmem : ρO ((p : ℕ) : A) ∈ RingHom.ker toκ := by
      rw [RingHom.mem_ker, ← RingHom.comp_apply, htoκ, map_natCast, CharP.cast_eq_zero]
    have hne : RingHom.ker toκ ≠ ⊥ := fun h => hpO (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    haveI : (RingHom.ker toκ).IsPrime := RingHom.ker_isPrime toκ
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

  have hsk : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO) = specMap A k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκ]
  let g := pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))

  let e := pullbackLeftPullbackSndIso (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)) (Spec.map (CommRingCat.ofHom toκ))
  let e2 : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO)) ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := pullback.congrHom rfl hsk
  let φ : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback g (Spec.map (CommRingCat.ofHom toκ)) := e2.inv ≫ e.inv
  have he2fst : e2.inv ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO)) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    simp only [e2, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]
  have he2snd : e2.inv ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom ρO)) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    simp only [e2, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
  have hφ : bc = φ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom toκ)) := by
    apply pullback.hom_ext
    · rw [hbc₁]
      change _ = ((e2.inv ≫ e.inv) ≫ _) ≫ _
      rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, he2fst]
    · rw [hbc₂]
      change _ = ((e2.inv ≫ e.inv) ≫ _) ≫ _
      rw [Category.assoc, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, ← Category.assoc, he2snd]

  have hgy : g.base y = (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint k) := by
    apply PrimeSpectrum.ext
    have h1 : (g.base y).asIdeal = IsLocalRing.maximalIdeal O := by
      have hϖy : ϖ ∈ (g.base y).asIdeal := by
        by_contra h
        exact hy ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
      refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (g.base y).2.ne_top ?_).symm
      rw [hϖ, Ideal.span_singleton_le_iff_mem]
      exact hϖy
    have h2 : ((Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint k)).asIdeal = IsLocalRing.maximalIdeal O := by
      change Ideal.comap toκ (IsLocalRing.closedPoint k).asIdeal = _
      rw [show (IsLocalRing.closedPoint k).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot, hker]
    rw [h1, h2]
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := Spec.map (CommRingCat.ofHom toκ)) y (IsLocalRing.closedPoint k) hgy

  let y' : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) := (e.hom ≫ e2.hom).base z
  have hφy' : φ.base y' = z := by
    change ((e.hom ≫ e2.hom) ≫ (e2.inv ≫ e.inv)).base z = z
    simp
  have hbcy' : bc.base y' = y := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.comp_app, hφy', hz1]

  rcases hcover y' with ⟨w, hw⟩ | ⟨w, hw⟩
  · left
    have : (i₁.1 ≫ bc).base w = y := by rw [Scheme.Hom.comp_base, TopCat.comp_app, hw, hbcy']
    rw [← this]
    exact (genericPoint_specializes w).map (i₁.1 ≫ bc).base.hom.continuous
  · right
    have : (i₂.1 ≫ bc).base w = y := by rw [Scheme.Hom.comp_base, TopCat.comp_app, hw, hbcy']
    rw [← this]
    exact (genericPoint_specializes w).map (i₂.1 ≫ bc).base.hom.continuous

end S_ModularCurve_XOneP_genericPoint_specializes_or_of_not_mem_basicOpen_baseChange_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_genericPoint_specializes_or_of_not_mem_basicOpen_baseChange_twoChartModel_x1_mul (solution)
