-- Prove2me | solution 1 for ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_snd_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3fd49951-52e3-5fc9-bf64-c280af17223d

import Mathlib
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_snd_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_snd_twoChartModel_x1_mul
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

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
      ∃ (V : ValuationSubring ↥K)
        (_ : ∀ a : A, algebraMap A ↥K a ∈ V)
        (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits)
        (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
        (algV : Algebra A ↥V) (_ : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a)
        (𝔮 : Ideal (TensorProduct A k ↥V)) (_ : 𝔮 ∈ minimalPrimes (TensorProduct A k ↥V)),
        Nonempty (F ≃ₐ[k] FractionRing (TensorProduct A k ↥V ⧸ 𝔮)) := by
  intro F _ _ Mdl e he
  classical

  let ξ : ↥C₂ := e.hom.base (genericPoint Mdl.C)
  have hξ : IsGenericPoint ξ ⊤ := by
    have h := (genericPoint_spec Mdl.C).image (f := e.hom.base) e.hom.base.hom.continuous
    have hsurj : Function.Surjective e.hom.base := (Scheme.homeoOfIso e).surjective
    rw [Set.image_univ, Set.range_eq_univ.mpr hsurj, closure_univ] at h
    exact h

  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : A, IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator (IsLocalRing.maximalIdeal A)).symm⟩

  set z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j) := (i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ with hzdef

  obtain ⟨hz, hdim⟩ :=
    ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_snd_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ w ϖ hϖ ξ hξ

  obtain ⟨𝔮₀, h𝔮₀, ⟨eF⟩⟩ :=
    ModularCurve.XOneP.exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_snd_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ w F Mdl e he ξ hξ

  obtain ⟨V, eV, hVA, hVm, hVj, -, hlin⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_ringEquiv_stalk_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ z _ rfl hz hdim

  letI algSt : Algebra A ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) :=
    RingHom.toAlgebra (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom.comp
      ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
  let algV : Algebra A ↥V := RingHom.toAlgebra ((algebraMap A ↥K).codRestrict V.toSubring.toSubsemiring hVA)
  letI := algV
  have halgV : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a := fun a => rfl

  let eA : ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃ₐ[A] ↥V :=
    AlgEquiv.ofRingEquiv (f := eV) (fun a => Subtype.ext (by
      rw [halgV]
      exact hlin a))

  let φ : TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃ₐ[k] TensorProduct A k ↥V :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) eA

  have hprime : (𝔮₀.map φ).IsPrime := by
    haveI : 𝔮₀.IsPrime := h𝔮₀.1.1
    exact Ideal.map_isPrime_of_equiv φ
  have hmin : 𝔮₀.map φ ∈ minimalPrimes (TensorProduct A k ↥V) := by
    refine ⟨⟨hprime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hle
    haveI := hq

    have hle' : q.comap φ ≤ 𝔮₀ := by
      intro x hx
      have hx' : φ x ∈ q := hx
      have : φ x ∈ 𝔮₀.map φ := by
        by_contra hnot
        exact absurd (hle hx') (by exact fun h => hnot (by
          obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective φ φ.surjective).mp h
          exact Ideal.mem_map_of_mem _ (by
            have : y = x := φ.injective (by simpa using hyx)
            exact this ▸ hy)))
      obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective φ φ.surjective).mp this
      have : y = x := φ.injective (by simpa using hyx)
      exact this ▸ hy
    have heq : q.comap φ = 𝔮₀ :=
      le_antisymm hle' (h𝔮₀.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hle')
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ φ.surjective).mp hx
    rw [← heq] at hy
    exact hy

  let ψ : (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ 𝔮₀) ≃ₐ[k]
      (TensorProduct A k ↥V ⧸ 𝔮₀.map φ) :=
    Ideal.quotientEquivAlg _ _ φ rfl
  haveI : (𝔮₀.map φ).IsPrime := hprime
  haveI : 𝔮₀.IsPrime := h𝔮₀.1.1
  exact ⟨V, hVA, hVm, hVj, algV, halgV, 𝔮₀.map φ, hmin, ⟨eF.trans
    (IsFractionRing.algEquivOfAlgEquiv
      (A := TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ 𝔮₀)
      (B := TensorProduct A k ↥V ⧸ 𝔮₀.map φ)
      (K := FractionRing (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ 𝔮₀))
      (L := FractionRing (TensorProduct A k ↥V ⧸ 𝔮₀.map φ)) ψ)⟩⟩

end S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_snd_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_snd_twoChartModel_x1_mul (solution)
