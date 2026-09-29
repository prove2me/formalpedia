-- Prove2me | solution 1 for ModularCurve.finite_fixedPoints_frobeniusPushforwardModL_comp_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/14f14e76-17e9-5b3e-9133-f11be9eec47a

import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPushforwardModL_comp_self
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

open ModularCurve AlgebraicCurve

namespace FrobeniusSquareFixedClasses

private theorem w_isCurveOver (K : Type*) [Field K] [PerfectField K]
    (N : ℕ) [NeZero N] :
    AlgebraicCurve.IsCurveOver K (ModularCurve.modularFunctionFieldFullC K N) :=
  ModularCurve.isCurveOver_modularFunctionFieldFullC K N

private theorem w_inputs (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (N : ℕ) [NeZero N] :
    ModularCurve.FrobeniusInputsModL K N ℓ :=
  ModularCurve.frobeniusInputsModL K N

private theorem w_constantsAreBase
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    AlgebraicCurve.ConstantsAreBase k F₀ :=
  AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen φ hφ

private theorem w_fixedPoints
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hC : AlgebraicCurve.ConstantsAreBase k F₀)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * AlgebraicCurve.genusFF K F ∧
      P.coeff 0 = (Nat.card k : ℤ) ^ AlgebraicCurve.genusFF K F ∧
      (∀ n : ℕ, 0 < n →
        (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]).Finite ∧
        (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
          (Nat.card k : ℂ) ^ n + 1 -
            (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) ∧
      ∀ n : ℕ, 0 < n →
        (Function.fixedPoints (⇑T)^[n]).Finite ∧
        (Nat.card (Function.fixedPoints (⇑T)^[n]) : ℂ) =
          (((P.map (Int.castRingHom ℂ)).roots.map (fun z => 1 - z ^ n)).prod) ∧
        ((Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P =
          Nat.card (Function.fixedPoints (⇑T)^[n])) ∧
        ∀ (ℓ : ℕ) [Fact ℓ.Prime],
          Nat.card (AddCommGroup.primaryComponent
            (Polynomial.aeval (R := ℤ) T.toIntLinearMap
              (Polynomial.X ^ n - 1 : Polynomial ℤ)).toAddMonoidHom.ker ℓ) =
            ℓ ^ (((Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P).natAbs.factorization ℓ) :=
  AlgebraicCurve.Pic0.exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
    k K F₀ F hfg hC hgen halg φ hφi hφ T hT

private theorem coeffMap_mem (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    {x : LaurentSeries (ZMod ℓ)} (hx : x ∈ modularFunctionFieldFullC (ZMod ℓ) N) :
    coeffMap (ZMod.castHom (dvd_refl ℓ) K) x ∈ modularFunctionFieldFullC K N := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    rw [coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdvd
  | algebraMap a =>
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact IntermediateField.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | inv y _ hy =>
    rw [map_inv₀]
    exact inv_mem hy
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz

private noncomputable def formEmb (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ)
    [NeZero N] : modularFunctionFieldFullC (ZMod ℓ) N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨coeffMap (ZMod.castHom (dvd_refl ℓ) K) x, coeffMap_mem K ℓ N x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem coe_formEmb (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ)
    [NeZero N] (x : modularFunctionFieldFullC (ZMod ℓ) N) :
    (formEmb K ℓ N x : LaurentSeries K) = coeffMap (ZMod.castHom (dvd_refl ℓ) K) x := rfl

private theorem divisorExpansionsC_finite (R : Type*) [Field R] (N : ℕ) [NeZero N] :
    (divisorExpansionsC R N).Finite := by
  classical
  let g : ℕ → LaurentSeries R := fun d =>
    if h : d = 0 then 0 else by haveI : NeZero d := ⟨h⟩; exact qExpand R d (jqModC R)
  refine ((Finset.range (N + 1)).finite_toSet.image g).subset ?_
  rintro x ⟨d, hne, hdvd, rfl⟩
  refine ⟨d, ?_, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd)))
  · simp only [g, dif_neg hne.ne]

private theorem mem_of_forall_mem (R : Type*) [Field R] (N : ℕ) [NeZero N]
    (E : IntermediateField R (modularFunctionFieldFullC R N))
    (hE : ∀ (x : modularFunctionFieldFullC R N), (x : LaurentSeries R) ∈ divisorExpansionsC R N → x ∈ E)
    (v : LaurentSeries R) (hv : v ∈ modularFunctionFieldFullC R N) :
    (⟨v, hv⟩ : modularFunctionFieldFullC R N) ∈ E := by
  induction hv using IntermediateField.adjoin_induction with
  | mem y hy => exact hE _ hy
  | algebraMap a => exact E.algebraMap_mem a
  | add y z hy0 hz0 hy hz =>
    have e : (⟨y + z, add_mem hy0 hz0⟩ : modularFunctionFieldFullC R N) = ⟨y, hy0⟩ + ⟨z, hz0⟩ :=
      Subtype.ext (IntermediateField.coe_add (modularFunctionFieldFullC R N) ⟨y, hy0⟩ ⟨z, hz0⟩).symm
    rw [e]
    exact add_mem hy hz
  | inv y hy0 ih =>
    have e : (⟨y⁻¹, inv_mem hy0⟩ : modularFunctionFieldFullC R N) = ⟨y, hy0⟩⁻¹ :=
      Subtype.ext (IntermediateField.coe_inv (modularFunctionFieldFullC R N) ⟨y, hy0⟩).symm
    rw [e]
    exact inv_mem ih
  | mul y z hy0 hz0 hy hz =>
    have e : (⟨y * z, mul_mem hy0 hz0⟩ : modularFunctionFieldFullC R N) = ⟨y, hy0⟩ * ⟨z, hz0⟩ :=
      Subtype.ext (IntermediateField.coe_mul (modularFunctionFieldFullC R N) ⟨y, hy0⟩ ⟨z, hz0⟩).symm
    rw [e]
    exact mul_mem hy hz

end FrobeniusSquareFixedClasses

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) (N : ℕ) [NeZero N] :
    (Function.fixedPoints
      (frobeniusPushforwardModL K N ℓ ∘ frobeniusPushforwardModL K N ℓ)).Finite := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI := FrobeniusSquareFixedClasses.w_isCurveOver (ZMod ℓ) N
  haveI := FrobeniusSquareFixedClasses.w_isCurveOver K N
  letI : Algebra (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N) :=
    (FrobeniusSquareFixedClasses.formEmb K ℓ N).toAlgebra
  have halgebraMap : ∀ x : modularFunctionFieldFullC (ZMod ℓ) N,
      algebraMap (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N) x =
        FrobeniusSquareFixedClasses.formEmb K ℓ N x := fun _ => rfl

  have hfg : ∃ s : Finset (modularFunctionFieldFullC (ZMod ℓ) N),
      IntermediateField.adjoin (ZMod ℓ) (s : Set (modularFunctionFieldFullC (ZMod ℓ) N)) = ⊤ := by
    refine ⟨((FrobeniusSquareFixedClasses.divisorExpansionsC_finite (ZMod ℓ) N).preimage
      Subtype.val_injective.injOn).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    rintro ⟨v, hv⟩ -
    exact FrobeniusSquareFixedClasses.mem_of_forall_mem (ZMod ℓ) N _
      (fun x hx => IntermediateField.subset_adjoin (ZMod ℓ) _ hx) v hv
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap (modularFunctionFieldFullC (ZMod ℓ) N)
      (modularFunctionFieldFullC K N))) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    refine FrobeniusSquareFixedClasses.mem_of_forall_mem K N _ (fun x hx => ?_) v hv
    obtain ⟨d, hne, hdvd, hx⟩ := hx
    haveI := hne
    refine IntermediateField.subset_adjoin K _
      ⟨⟨qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)), jqModCd_mem_full (ZMod ℓ) N hdvd⟩, Subtype.ext ?_⟩
    rw [halgebraMap, FrobeniusSquareFixedClasses.coe_formEmb, coeffMap_qExpand, coeffMap_jqModC]
    exact hx.symm

  have hφ : ∀ x : modularFunctionFieldFullC (ZMod ℓ) N,
      frobeniusModL K N ℓ (algebraMap _ (modularFunctionFieldFullC K N) x) =
        algebraMap _ (modularFunctionFieldFullC K N) (x ^ Nat.card (ZMod ℓ)) := by
    intro x
    apply Subtype.ext
    rw [Nat.card_zmod, halgebraMap, halgebraMap, coe_frobeniusModL,
      FrobeniusSquareFixedClasses.coe_formEmb, FrobeniusSquareFixedClasses.coe_formEmb,
      SubmonoidClass.coe_pow, pow_char_eq_coeffMap_frobenius_qExpand, ZMod.frobenius_zmod,
      coeffMap_id, coeffMap_qExpand]
  have hC := FrobeniusSquareFixedClasses.w_constantsAreBase (ZMod ℓ) K
    (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N) hfg hgen
    (frobeniusModL K N ℓ) hφ
  have halg' : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card (ZMod ℓ) ^ n = a := by
    intro a
    rw [Nat.card_zmod]
    exact halg a

  have hinputs := FrobeniusSquareFixedClasses.w_inputs K N (ℓ := ℓ)
  obtain ⟨hP, hfin, hFI, hN⟩ := hinputs
  haveI := hP
  have hT : ∀ D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N),
      frobeniusPushforwardModL K N ℓ (Pic0.mk D) =
        Pic0.mk ⟨Divisor.pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) D,
          Divisor.pushforwardAlong_mem_degZero (frobeniusModL K N ℓ)
            (frobeniusModL_isIntegral K N ℓ) D.2⟩ := by
    intro D
    rw [frobeniusPushforwardModL_mk hfin hFI hN]
    rfl
  have hmain :=
    FrobeniusSquareFixedClasses.w_fixedPoints
      (ZMod ℓ) K (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N) hfg hC hgen
      halg' (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) hφ (frobeniusPushforwardModL K N ℓ)
      hT
  obtain ⟨P, -, -, -, -, hfix⟩ := hmain
  have h2 := (hfix 2 two_pos).1
  rwa [Function.iterate_succ', Function.iterate_one] at h2

end S_ModularCurve_finite_fixedPoints_frobeniusPushforwardModL_comp_self
end P2MW
export P2MW.S_ModularCurve_finite_fixedPoints_frobeniusPushforwardModL_comp_self (solution)
