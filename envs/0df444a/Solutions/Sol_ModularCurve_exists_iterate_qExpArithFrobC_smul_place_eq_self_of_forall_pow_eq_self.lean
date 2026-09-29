-- Prove2me | solution 1 for ModularCurve.exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0d69a01d-9bcf-5d8f-bbf4-8728295e181b

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups Pointwise

namespace PlacePeriodic

variable {K : Type} [Field K]

noncomputable def formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) :=
  letI := ι₀.toAlgebra
  have hmem : ∀ x : ↥(qExpFunctionFieldC k Γ), coeffMap (algebraMap k K) (x : LaurentSeries k) ∈ qExpFunctionFieldC K Γ := by
    intro x
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩
  { toFun := fun x => ⟨coeffMap (algebraMap k K) (x : LaurentSeries k), hmem x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun x y => Subtype.ext (by simp) }

theorem coe_formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC k Γ)) :
    (formEmb ι₀ Γ x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries k) := rfl

theorem smul_formEmb_of_forall_apply_eq {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ))
    (g : SemilinearAut K ↥(qExpFunctionFieldC K Γ)) (τ : K →+* K)
    (hg : ∀ y : ↥(qExpFunctionFieldC K Γ), ((g • y : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap τ (y : LaurentSeries K))
    (hτ : ∀ a : k, τ (ι₀ a) = ι₀ a) (x : ↥(qExpFunctionFieldC k Γ)) :
    g • formEmb ι₀ Γ x = formEmb ι₀ Γ x := by
  apply Subtype.ext
  rw [hg, coe_formEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext hτ) _

theorem smul_eq_of_forall_apply_eq {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ))
    (ι : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(qExpFunctionFieldC k Γ), (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries k))
    (g : SemilinearAut K ↥(qExpFunctionFieldC K Γ)) (τ : K →+* K)
    (hg : ∀ y : ↥(qExpFunctionFieldC K Γ), ((g • y : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap τ (y : LaurentSeries K))
    (hτ : ∀ a : k, τ (ι₀ a) = ι₀ a) (x : ↥(qExpFunctionFieldC k Γ)) :
    g • ι x = ι x := by
  apply Subtype.ext
  rw [hg, hι, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext hτ) _

end PlacePeriodic

open PlacePeriodic in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    ∃ j : ℕ, 0 < j ∧ (fun v : Place K ↥(qExpFunctionFieldC K Γ) => qExpArithFrobC p K Γ • v)^[j] w = w := by
  classical
  have hp : p.Prime := Fact.out
  set σ := qExpArithFrobC p K Γ with hσ
  have hiter : ∀ (j : ℕ) (v : Place K ↥(qExpFunctionFieldC K Γ)), (fun v : Place K ↥(qExpFunctionFieldC K Γ) => σ • v)^[j] v = σ ^ j • v := by
    intro j; induction j with
    | zero => intro v; simp
    | succ j ih => intro v; rw [Function.iterate_succ_apply', ih, ← mul_smul, ← pow_succ']
  have hpow : ∀ (n : ℕ) (y : ↥(qExpFunctionFieldC K Γ)), ((σ ^ n • y : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap ((frobenius K p) ^ n) (y : LaurentSeries K) := by
    intro n
    induction n with
    | zero =>
      intro y
      rw [pow_zero, one_smul, pow_zero]
      exact (coeffMap_id _).symm
    | succ n ih =>
      intro y
      rw [pow_succ, mul_smul, ih (σ • y), hσ, coe_qExpArithFrobC_smul, coeffMap_coeffMap, ← RingHom.mul_def,
        ← pow_succ]

  obtain ⟨m, hm, ι₀, ι, hι, P, hPO, hPdeg⟩ :=
    ModularCurve.exists_place_qExpFunctionFieldC_galoisField_toValuationSubring_eq_comap_and_deg_eq_one K p halg Γ hT w

  letI : Algebra (GaloisField p m) K := ι₀.toAlgebra
  letI : Algebra ↥(qExpFunctionFieldC (GaloisField p m) Γ) ↥(qExpFunctionFieldC K Γ) := ι.toAlgebra
  letI : Algebra (GaloisField p m) ↥(qExpFunctionFieldC K Γ) := ((algebraMap K ↥(qExpFunctionFieldC K Γ)).comp ι₀).toAlgebra
  haveI : IsScalarTower (GaloisField p m) K ↥(qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) ↥(qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext ?_)
    show ((algebraMap K ↥(qExpFunctionFieldC K Γ) (ι₀ a) : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = (ι (algebraMap (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) a) : LaurentSeries K)
    rw [hι]
    change algebraMap K (LaurentSeries K) (ι₀ a) =
      coeffMap ι₀ (algebraMap (GaloisField p m) (LaurentSeries (GaloisField p m)) a)
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  have huniq : ∀ Q₁ Q₂ : Place K ↥(qExpFunctionFieldC K Γ),
      Q₁.toValuationSubring.comap (algebraMap _ ↥(qExpFunctionFieldC K Γ)) = P.toValuationSubring →
      Q₂.toValuationSubring.comap (algebraMap _ ↥(qExpFunctionFieldC K Γ)) = P.toValuationSubring → Q₁ = Q₂ := by
    haveI : Fintype (GaloisField p m) := Fintype.ofFinite _
    haveI : PerfectField (GaloisField p m) := inferInstance

    haveI : Algebra.IsAlgebraic (GaloisField p m) K := by
      refine ⟨fun a => ?_⟩
      obtain ⟨n, hn, ha⟩ := halg a
      have h1 : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.one_lt
      refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.X, FiniteField.X_pow_card_sub_X_ne_zero _ h1, ?_⟩
      simp [ha]

    set xj : ↥(qExpFunctionFieldC (GaloisField p m) Γ) := ⟨jqModC (GaloisField p m), intFormRatiosC_subset (GaloisField p m) Γ (ModularCurve.jqModC_mem_intFormRatiosC (GaloisField p m) Γ)⟩ with hxj
    have hxjt : Transcendental (GaloisField p m) xj := by
      intro halgj
      apply ModularCurve.transcendental_jqModC (GaloisField p m)
      exact halgj.algebraMap (A := LaurentSeries (GaloisField p m))
    obtain ⟨hfdj, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (GaloisField p m) Γ hT Γ le_rfl
      (fun γ hγ => Or.inl hγ) xj rfl
    haveI := hfdj
    haveI : IsCurveOver (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxjt hfdj
    haveI : HasPrincipalDivisors (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := IsCurveOver.hasPrincipalDivisors
    have hC : ConstantsAreBase (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := AlgebraicCurve.constantsAreBase_of_deg_eq_one P hPdeg
    obtain ⟨x', -, hx't, hx'fd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT

    have hgen : IntermediateField.adjoin K (Set.range (algebraMap ↥(qExpFunctionFieldC (GaloisField p m) Γ) ↥(qExpFunctionFieldC K Γ))) = ⊤ := by
      apply IntermediateField.lift_injective (qExpFunctionFieldC K Γ)
      have e1 := IntermediateField.lift_adjoin K (qExpFunctionFieldC K Γ)
        (Set.range (algebraMap ↥(qExpFunctionFieldC (GaloisField p m) Γ) ↥(qExpFunctionFieldC K Γ)))
      have e2 := IntermediateField.lift_top K (qExpFunctionFieldC K Γ)
      refine e1.trans (Eq.trans ?_ e2.symm)
      conv_rhs => rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC (GaloisField p m) K Γ]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, z.2, (hι z).symm⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨ι ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, hι ⟨z, hz⟩⟩
    obtain ⟨P', -, -, hP'⟩ :=
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
        (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) K ↥(qExpFunctionFieldC K Γ) ⟨xj, hxjt, hfdj⟩ ⟨x', hx't, hx'fd⟩ hC hgen P hPdeg
    intro Q₁ Q₂ h₁ h₂
    rw [hP' Q₁ h₁, hP' Q₂ h₂]

  have hfix : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ), σ ^ m • ι x = ι x := by
    intro x
    refine smul_eq_of_forall_apply_eq ι₀ Γ ι hι (σ ^ m) ((frobenius K p) ^ m) ?_ ?_ x
    · exact hpow m
    · intro a
      haveI : Fintype (GaloisField p m) := Fintype.ofFinite _
      rw [RingHom.coe_pow, iterate_frobenius, ← map_pow]
      congr 1
      have hcard : Fintype.card (GaloisField p m) = p ^ m := by
        rw [Fintype.card_eq_nat_card]; exact GaloisField.card p m hm.ne'
      rw [← hcard, FiniteField.pow_card]
  have hover : (σ ^ m • w).toValuationSubring.comap (algebraMap _ ↥(qExpFunctionFieldC K Γ)) = P.toValuationSubring := by
    rw [hPO]
    ext x
    simp only [ValuationSubring.mem_comap]
    show ι x ∈ (σ ^ m • w).toValuationSubring ↔ ι x ∈ w.toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring]
    conv_lhs => rw [← hfix x]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨m, hm, ?_⟩
  rw [hiter]
  exact huniq _ _ hover hPO.symm

end S_ModularCurve_exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
end P2MW
export P2MW.S_ModularCurve_exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self (solution)
