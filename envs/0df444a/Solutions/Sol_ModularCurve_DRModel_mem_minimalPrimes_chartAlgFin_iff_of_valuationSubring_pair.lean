-- Prove2me | solution 1 for ModularCurve.DRModel.mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7665f6f9-a5e6-5b95-ac22-cee22737a41a

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair.ModularCurve AlgebraicCurve Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme qExpand jq modularFunctionFieldFull transcendental_jq finiteDimensional_adjoin_jFull_modularFunctionFieldFull"
namespace DRModel
namespace MinPrimesAux
p2m_open "ModularCurve"

theorem map_castRingHom_zmod_eq_zero_iff (p : ℕ) (P : Polynomial ℤ) :
    P.map (Int.castRingHom (ZMod p)) = 0 ↔ C (p : ℤ) ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun n => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem not_mem_nonunits_of_inv_mem {K : Type*} [Field K] (W : ValuationSubring K) {x : K}
    (hx0 : x ≠ 0) (hx : x ∈ W) (hinv : x⁻¹ ∈ W) : x ∉ W.nonunits := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff] at h
  have h1 : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hinv
  have hpos : 0 < W.valuation x := zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hx0)
  rw [map_inv₀, inv_le_one₀ hpos] at h1
  exact (lt_irrefl _) (lt_of_lt_of_le h h1)

theorem mem_of_isIntegral_adjoin {K : Type*} [Field K] (W : ValuationSubring K) (s : Set K)
    (hs : s ⊆ W) (x : K) (hx : IsIntegral ↥(Algebra.adjoin ℤ s) x) : x ∈ W := by
  have hle : ∀ y ∈ Algebra.adjoin ℤ s, y ∈ W := by
    intro y hy
    have : Algebra.adjoin ℤ s ≤ subalgebraOfSubring W.toSubring := Algebra.adjoin_le hs
    exact this hy
  let φ : ↥(Algebra.adjoin ℤ s) →+* ↥W :=
    (Algebra.adjoin ℤ s).val.toRingHom.codRestrict W.toSubring fun y => hle y y.2
  have hx' : IsIntegral ↥W x :=
    hx.map_of_comp_eq φ (RingHom.id K) (by ext; rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := K)).mp hx'
  rw [← hy]
  exact y.2

end ModularCurve.DRModel.MinPrimesAux

end

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits) :
    let A := TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    ∀ 𝔭 : Ideal ↥A, 𝔭 ∈ (Ideal.span {((p : ℕ) : ↥A)}).minimalPrimes ↔
        ((∀ a : ↥A, a ∈ 𝔭 ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)) ∨
         (∀ a : ↥A, a ∈ 𝔭 ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits))) := by
  intro A 𝔭
  classical

  have hpprime : (p : ℕ).Prime := Fact.out
  have hϖ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpprime
  have hW : ∀ i : Fin 2, (![W₀, W₁] i) = W₀ ∨ (![W₀, W₁] i) = W₁ := by
    intro i; fin_cases i <;> simp

  have hmapC : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 ↔ ¬ (C (p : ℤ) ∣ P) := fun P =>
    (ModularCurve.DRModel.MinPrimesAux.map_castRingHom_zmod_eq_zero_iff p P).not
  have haeval : ∀ P : Polynomial ℤ,
      Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p) P =
        aeval (IgusaScheme.jFull p) P := fun P => rfl
  have hpcast : ((p : ℤ) : ↥(modularFunctionFieldFull p)) = ((p : ℕ) : ↥(modularFunctionFieldFull p)) := by
    push_cast; rfl

  have hjW : ∀ i : Fin 2, (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i) := by
    intro i
    have := (hgen i X (by rw [Polynomial.map_X]; exact X_ne_zero)).1
    simpa only [eval₂_X] using this
  have hAW : ∀ i : Fin 2, ∀ a : ↥A, (a : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i) := by
    intro i a
    refine ModularCurve.DRModel.MinPrimesAux.mem_of_isIntegral_adjoin _ {IgusaScheme.jFull p}
      (Set.singleton_subset_iff.mpr (hjW i)) _ ?_
    exact (TwoChartIntegralModel.mem_chartAlg_iff ℤ ↥(modularFunctionFieldFull p)).mp a.2

  have htjℚ : Transcendental ℚ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := by
    intro halg
    obtain ⟨q, hq, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨q, hq, ?_⟩
    have h0 : (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ))
        ((Polynomial.aeval (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))) q) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from
          IgusaScheme.coe_jFull p] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ℤ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ↥(modularFunctionFieldFull p)).mp h)
  have haeval0 : ∀ P : Polynomial ℤ, P ≠ 0 →
      (aeval (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P) ≠ 0 := fun P hP h =>
    hP (transcendental_iff_injective.mp htj (by rw [h, map_zero]))
  have hFD := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  haveI := hFD
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
      ↥(modularFunctionFieldFull p) := inferInstance
  have hspan : Ideal.span {algebraMap ℤ ↥A (p : ℤ)} = Ideal.span {((p : ℕ) : ↥A)} := by
    rw [map_natCast]

  have hS0 : ∀ 𝔮 : Ideal ↥A, 𝔮 ∈ (Ideal.span {((p : ℕ) : ↥A)}).minimalPrimes →
      ∃ V : ValuationSubring ↥(modularFunctionFieldFull p),
        (∀ f : ↥A, f ∈ 𝔮 ↔ (f : ↥(modularFunctionFieldFull p)) ∈ V.nonunits) ∧
        (V = W₀ ∨ V = W₁) ∧
        (∀ P : Polynomial ℤ, ¬ (C (p : ℤ) ∣ P) →
          (⟨aeval (IgusaScheme.jFull p) P,
            TwoChartIntegralModel.adjoin_le_chartAlg ℤ _ _ (Polynomial.aeval_mem_adjoin_singleton ℤ _)⟩ : ↥A) ∉ 𝔮) := by
    intro 𝔮 h𝔮
    rw [← hspan] at h𝔮
    obtain ⟨V, -, -, hcen, hpV, hgenV⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin ℤ ℚ
        ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) htj hFD hsep (p : ℤ) hϖ 𝔮 h𝔮
    refine ⟨V, hcen, ?_, ?_⟩
    · apply hcomplete V
      · have : algebraMap ℤ ↥(modularFunctionFieldFull p) (p : ℤ) =
            ((p : ℕ) : ↥(modularFunctionFieldFull p)) := by simp
        rw [← this]; exact hpV
      · intro P hP
        rw [haeval]
        exact hgenV P ((hmapC P).mp hP)
    · intro P hP hmem
      have h1 := (hcen _).mp hmem
      have hP0 : P ≠ 0 := fun h => hP (h ▸ dvd_zero _)
      exact ModularCurve.DRModel.MinPrimesAux.not_mem_nonunits_of_inv_mem V (haeval0 P hP0)
        (hgenV P hP).1 (hgenV P hP).2 h1
  constructor
  ·
    intro h𝔭
    obtain ⟨V, hcen, hV, -⟩ := hS0 𝔭 h𝔭
    rcases hV with rfl | rfl
    · exact Or.inl hcen
    · exact Or.inr hcen
  ·
    intro hcases

    obtain ⟨i, h𝔭i⟩ : ∃ i : Fin 2, ∀ a : ↥A, a ∈ 𝔭 ↔
        (a : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i).nonunits := by
      rcases hcases with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    have hpi : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i).nonunits := by
      fin_cases i
      · simpa using hp₀
      · simpa using hp₁

    let toW : ↥A →+* ↥(![W₀, W₁] i) :=
      A.val.toRingHom.codRestrict (![W₀, W₁] i).toSubring fun a => hAW i a
    have h𝔭eq : 𝔭 = (IsLocalRing.maximalIdeal ↥(![W₀, W₁] i)).comap toW := by
      ext a
      rw [h𝔭i, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
      rfl
    haveI h𝔭prime : 𝔭.IsPrime := by rw [h𝔭eq]; exact Ideal.IsPrime.comap _
    have hp𝔭 : ((p : ℕ) : ↥A) ∈ 𝔭 := by
      rw [h𝔭i]; simpa using hpi

    obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔭)
    suffices h : 𝔮 = 𝔭 by rw [← h]; exact h𝔮min
    haveI : 𝔮.IsPrime := h𝔮min.1.1
    obtain ⟨V, hcen, -, hgen𝔮⟩ := hS0 𝔮 h𝔮min
    by_contra hne𝔮
    have hlt : 𝔮 < 𝔭 := lt_of_le_of_ne h𝔮le hne𝔮

    have hBA : Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)) ≤ A :=
      TwoChartIntegralModel.adjoin_le_chartAlg ℤ _ {IgusaScheme.jFull p}
    letI : Algebra ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) ↥A :=
      (Subalgebra.inclusion hBA).toAlgebra
    haveI : IsScalarTower ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) ↥A
        ↥(modularFunctionFieldFull p) := IsScalarTower.of_algebraMap_eq fun x => rfl
    have hint : ∀ x : ↥A,
        IsIntegral ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) x := by
      intro x
      have hx : IsIntegral ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
          (x : ↥(modularFunctionFieldFull p)) := (TwoChartIntegralModel.mem_chartAlg_iff ℤ _).mp x.2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ ↥A ↥(modularFunctionFieldFull p))
        Subtype.val_injective).mp hx
    obtain ⟨x, hx𝔭, hx𝔮⟩ := Set.exists_of_ssubset hlt
    have hlt' := Ideal.comap_lt_comap_of_integral_mem_sdiff
      (R := ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))))
      h𝔮le ⟨hx𝔭, hx𝔮⟩ (hint x)
    obtain ⟨b, hb𝔭, hb𝔮⟩ := Set.exists_of_ssubset hlt'

    let e := Polynomial.algEquivOfTranscendental ℤ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) htj
    have hecoe : ∀ P : Polynomial ℤ,
        ((e P : ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))) :
          ↥(modularFunctionFieldFull p)) = aeval (IgusaScheme.jFull p) P :=
      fun P => by simp [e, Polynomial.algEquivOfTranscendental]
    obtain ⟨P, hPb⟩ := e.surjective b
    have halg : ∀ Q : Polynomial ℤ,
        algebraMap ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) ↥A (e Q) =
          (⟨aeval (IgusaScheme.jFull p) Q,
            TwoChartIntegralModel.adjoin_le_chartAlg ℤ _ _ (Polynomial.aeval_mem_adjoin_singleton ℤ _)⟩ : ↥A) :=
      fun Q => Subtype.ext (hecoe Q)
    have hPdvd : ¬ (C (p : ℤ) ∣ P) := by
      rintro ⟨P', hP'⟩
      apply hb𝔮
      rw [SetLike.mem_coe, Ideal.mem_comap, ← hPb, hP', map_mul, map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have : algebraMap ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) ↥A
          (e (C (p : ℤ))) = ((p : ℕ) : ↥A) := by
        rw [halg]
        apply Subtype.ext
        simp
      rw [this]
      exact h𝔮min.1.2 (Ideal.subset_span rfl)

    have hmem : (⟨aeval (IgusaScheme.jFull p) P,
        TwoChartIntegralModel.adjoin_le_chartAlg ℤ _ _ (Polynomial.aeval_mem_adjoin_singleton ℤ _)⟩ : ↥A) ∈ 𝔭 := by
      rw [SetLike.mem_coe, Ideal.mem_comap, ← hPb, halg] at hb𝔭
      exact hb𝔭
    have h1 := (h𝔭i _).mp hmem
    have h2 := hgen i P ((hmapC P).mpr hPdvd)
    have hP0 : P ≠ 0 := fun h => hPdvd (h ▸ dvd_zero _)
    exact ModularCurve.DRModel.MinPrimesAux.not_mem_nonunits_of_inv_mem _ (haeval0 P hP0) h2.1 h2.2 h1

end S_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair
end P2MW
export P2MW.S_ModularCurve_DRModel_mem_minimalPrimes_chartAlgFin_iff_of_valuationSubring_pair (solution)
