-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_smul_mem_and_inv_mem_gauss_levelField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e21af208-9146-5cbc-aa89-2e1bc631c6d4

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation
import Theorems.Thm_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_smul_mem_and_inv_mem_gauss_levelField
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel IsLocalRing

set_option maxHeartbeats 51200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK' : FiniteDimensional ↥k₀ ↥K')
    (A' : ValuationSubring ↥K') (hA' : ∀ x : ↥K', x ∈ A' ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A'] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤ →

      (∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →

      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ (O : ValuationSubring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ O ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) →
    (∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      f ≠ 0 → ∃ c : ↥K', c ≠ 0 ∧
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) * (f : ↥(fieldBar q M')) ∈ O ∧
        (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) * (f : ↥(fieldBar q M')))⁻¹ ∈ O) ∧
    (∀ ϖ' : ↥A', maximalIdeal ↥A' = Ideal.span {ϖ'} →
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀),
        (f : ↥(fieldBar q M')) ∈ O.nonunits →
        ∃ g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀),
          (g : ↥(fieldBar q M')) ∈ O ∧
          (f : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' : ↥K') : AlgebraicClosure ℚ) * (g : ↥(fieldBar q M'))) := by
  intro F₀ hK1 hLD hRAT O hO
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨e, he⟩ := ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap q M' k₀ K' hK'
    F₀ hK1 hLD hRAT

  letI algAK : Algebra ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) := ((algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))).comp (algebraMap ↥A' ↥K')).toAlgebra
  haveI hsc : @IsScalarTower ↥A' ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) inferInstance inferInstance algAK.toSMul :=
    @IsScalarTower.of_algebraMap_eq ↥A' ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) _ _ _ _ _ algAK (fun _ => rfl)
  have hAK : ∀ a : ↥A', ((algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) a : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K') = HahnSeries.single 0 ((a : ↥K')) := fun a => by
    rw [← algebraMap_laurentSeries_eq_single]; rfl

  have hjq : jq ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) := by
    refine x0_le_xHFunctionFieldC (K := ℚ) (M := q ^ 2 * M') (H := levelH q M') ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact modularFunctionField_le_full _ (jq_mem _)
  let jK : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) := ⟨coeffEmb ↥K' jq, coeffEmb_mem_laurentBaseChange ↥K' hjq⟩
  haveI : Fact (jK ≠ 0) := ⟨fun h0 => jq_ne_zero (by
    have h1 : coeffEmb ↥K' jq = 0 := congrArg Subtype.val h0
    have h2 := congrArg (fun s => HahnSeries.coeff s (-1 : ℤ)) h1
    simp only [coeffEmb, coeffMap_coeff, coeff_jq_neg_one, map_one] at h2
    exact absurd h2 (by simp))⟩

  obtain ⟨W₀, hW₀, hconst, hmax, -, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) ↥K'
      (laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) rfl ↥A' jK rfl

  let φ : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) →+* ↥(fieldBar q M') := (algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M')).comp e.toRingHom
  have hφe : ∀ f, φ f = ((e f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) := fun _ => rfl
  have hφ : ∀ f : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))), ((φ f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K' (AlgebraicClosure ℚ)) ((f : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K') := fun f => he f
  obtain ⟨hbr1, hbr2⟩ :=
    ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap k₀ K' A A' hA'
      (laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) W₀ hW₀ (fieldBar q M') O hO φ hφ

  have hφc : ∀ c : ↥K', φ (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) c) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := by
    intro c
    apply Subtype.ext
    rw [hφ, show ((algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) c : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries ↥K') = HahnSeries.single 0 c from by
      rw [← algebraMap_laurentSeries_eq_single]; rfl, coeffMap_single]
    show HahnSeries.single 0 ((c : ↥K') : AlgebraicClosure ℚ) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((c : ↥K') : AlgebraicClosure ℚ)
    rw [algebraMap_laurentSeries_eq_single]
  have hφe' : ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀), φ (e.symm f) = (f : ↥(fieldBar q M')) := fun f => by rw [hφe, e.apply_symm_apply]
  refine ⟨?_, ?_⟩
  ·

    obtain ⟨ϖ', hϖ'irr⟩ := IsDiscreteValuationRing.exists_irreducible ↥A'
    have hϖ' : maximalIdeal ↥A' = Ideal.span {ϖ'} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ'irr
    have hϖ'0 : (ϖ' : ↥K') ≠ 0 := fun h => hϖ'irr.ne_zero (Subtype.ext h)
    have hPdef : algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ϖ' = algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K') := rfl
    have hP0 : algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ϖ' ≠ 0 := by rw [hPdef]; exact (map_ne_zero _).mpr hϖ'0
    have hϖW : algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ϖ' ∈ W₀.nonunits := hmax ϖ' hϖ'irr.not_isUnit
    have hne : W₀ ≠ ⊤ := by
      intro htop
      rw [ValuationSubring.mem_nonunits_iff_or] at hϖW
      rcases hϖW with h0 | hinv
      · exact hP0 h0
      · exact hinv (htop ▸ (ValuationSubring.mem_top _))
    haveI hDVR : IsDiscreteValuationRing ↥W₀ :=
      ValuationSubring.isDiscreteValuationRing_of_forall_mem_iff_gaussPresentation
        (algebraMap ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (LaurentSeries ↥K')) W₀ hW₀ hne
    let ϖ₀ : ↥W₀ := ⟨algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ϖ', hconst ϖ'⟩
    have hmaxW : maximalIdeal ↥W₀ = Ideal.span {ϖ₀} := by
      apply le_antisymm
      · intro x hx
        have hxnu : (x : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) ∈ W₀.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hx
        obtain ⟨g, hg, hxg⟩ := ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation ↥K'
          (laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ↥A' ϖ' hϖ' W₀ hW₀ (x : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) hxnu
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨g, hg⟩, Subtype.ext (by rw [MulMemClass.coe_mul, hxg]; exact mul_comm _ _)⟩
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ← ValuationSubring.coe_mem_nonunits_iff]
        exact hϖW
    have hirr : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hmaxW

    intro f hf0
    let f₀ : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) := e.symm f
    have hf₀0 : f₀ ≠ 0 := (map_ne_zero_iff _ e.symm.injective).mpr hf0
    have key : ∃ c : ↥K', c ≠ 0 ∧ algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) c * f₀ ∈ W₀ ∧ (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) c * f₀)⁻¹ ∈ W₀ := by
      have unit_inv_mem : ∀ u : (↥W₀)ˣ, ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))))⁻¹ ∈ W₀ := by
        intro u
        have h1 : ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) * (((u⁻¹ : (↥W₀)ˣ) : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) = 1 := by
          rw [← MulMemClass.coe_mul, show ((u : ↥W₀) * ((u⁻¹ : (↥W₀)ˣ) : ↥W₀)) = 1 from u.mul_inv, OneMemClass.coe_one]
        rw [← eq_inv_of_mul_eq_one_right h1]
        exact ((u⁻¹ : (↥W₀)ˣ) : ↥W₀).2
      have hPn : ∀ n : ℕ, ((ϖ₀ ^ n : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) = (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K')) ^ n := fun n => by
        rw [SubmonoidClass.coe_pow]; rfl
      have hPK0 : algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K') ≠ 0 := (map_ne_zero _).mpr hϖ'0
      rcases W₀.mem_or_inv_mem f₀ with hmem | hinv
      · have hx0 : (⟨f₀, hmem⟩ : ↥W₀) ≠ 0 := fun h => hf₀0 (congrArg Subtype.val h)
        obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
        have hu' : f₀ = ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) * (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K')) ^ n := by
          have := congrArg Subtype.val hu
          rw [MulMemClass.coe_mul, hPn] at this
          exact this
        have hcf : algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (((ϖ' : ↥K')⁻¹) ^ n) * f₀ = ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) := by
          have hc : (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K'))⁻¹ ^ n * (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K')) ^ n = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hPK0, one_pow]
          rw [hu', map_pow, map_inv₀, mul_comm (((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))))), ← mul_assoc, hc, one_mul]
        refine ⟨((ϖ' : ↥K')⁻¹) ^ n, pow_ne_zero _ (inv_ne_zero hϖ'0), ?_, ?_⟩
        · rw [hcf]; exact (u : ↥W₀).2
        · rw [hcf]; exact unit_inv_mem u
      · have hx0 : (⟨f₀⁻¹, hinv⟩ : ↥W₀) ≠ 0 := fun h => (inv_ne_zero hf₀0) (congrArg Subtype.val h)
        obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
        have hu' : f₀⁻¹ = ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) * (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K')) ^ n := by
          have := congrArg Subtype.val hu
          rw [MulMemClass.coe_mul, hPn] at this
          exact this
        have hu0 : ((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))) ≠ 0 := by
          intro h0
          have := hu'
          rw [h0, zero_mul, inv_eq_zero] at this
          exact hf₀0 this
        have hcf : algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ((ϖ' : ↥K') ^ n) * f₀ = (((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))))⁻¹ := by
          rw [map_pow, ← inv_inv f₀, hu', mul_inv, mul_comm (((u : ↥W₀) : ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M')))))⁻¹, ← mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ hPK0), one_mul]
        refine ⟨(ϖ' : ↥K') ^ n, pow_ne_zero _ hϖ'0, ?_, ?_⟩
        · rw [hcf]; exact unit_inv_mem u
        · rw [hcf, inv_inv]; exact (u : ↥W₀).2
    obtain ⟨c, hc0, hcW, hcW'⟩ := key
    have hφcf : φ (algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) c * f₀) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) * (f : ↥(fieldBar q M')) := by
      rw [map_mul, hφc, hφe']
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [← hφcf]; exact (hbr1 _).mp hcW
    · rw [← hφcf, ← map_inv₀]; exact (hbr1 _).mp hcW'
  ·
    intro ϖ' hϖ' f hf
    have hPdef : algebraMap ↥A' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ϖ' = algebraMap ↥K' ↥(laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) (ϖ' : ↥K') := rfl
    have hf₀ : e.symm f ∈ W₀.nonunits := by rw [hbr2, hφe']; exact hf
    obtain ⟨g₀, hg₀, hfg⟩ := ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation ↥K'
      (laurentBaseChange ↥K' (xHFunctionField (q ^ 2 * M') (levelH q M'))) ↥A' ϖ' hϖ' W₀ hW₀ (e.symm f) hf₀
    refine ⟨e g₀, ?_, ?_⟩
    · rw [← hφe]; exact (hbr1 g₀).mp hg₀
    · rw [← hφe' f, hfg, map_mul, hφe g₀, hPdef, hφc]

end S_ModularCurve_FullLevel_exists_smul_mem_and_inv_mem_gauss_levelField
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_smul_mem_and_inv_mem_gauss_levelField (solution)
