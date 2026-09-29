-- Prove2me | solution 1 for ModularCurve.exists_algHom_laurentBaseChange_slot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7fced64d-979b-58ce-a91c-dc2288b3bb24

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_laurentBaseChange_slot
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open ModularCurve AlgebraicCurve Polynomial IntermediateField

namespace CD

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem qExpand_coeffEmb (N : ℕ) [NeZero N] (f : LaurentSeries ℚ) :
    qExpand K N (coeffEmb K f) = coeffEmb K (qExpand ℚ N f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, coeffEmb_coeff, coeffEmb_coeff, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hk, coeffEmb_coeff, qExpand_coeff_of_not_dvd N _ hk,
      map_zero]

theorem laurentBaseChange_full_eq_adjoin_adjoin (N : ℕ) [NeZero N] :
    laurentBaseChange K (modularFunctionFieldFull N) =
      (K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯).restrictScalars K := by
  rw [laurentBaseChange_adjoin_pair K N (functionFieldGeneration N), ← coeffEmb_jq,
    ← coeffEmb_jqN]
  exact (adjoin_simple_adjoin_simple K (coeffEmb K jq) (coeffEmb K (jqN N))).symm

theorem finrank_adjoin_adjoin (N : ℕ) [NeZero N] :
    Module.finrank K⟮coeffEmb K jq⟯ K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯ = dedekindPsi N := by
  have hle : K⟮coeffEmb K jq⟯ ≤ laurentBaseChange K (modularFunctionFieldFull N) :=
    adjoin_simple_le_iff.mpr (coeffEmb_mem_laurentBaseChange K (jq_mem_full N))
  have h := relfinrank_laurentBaseChange_modularFunctionFieldFull K N
  rw [relfinrank_full_eq_dedekindPsi, relfinrank_eq_finrank_of_le hle] at h
  have hext : extendScalars hle = K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯ :=
    restrictScalars_injective K
      ((extendScalars_restrictScalars hle).trans (laurentBaseChange_full_eq_adjoin_adjoin K N))
  rwa [hext] at h

theorem isIntegral_jqN (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N) := by
  have hfin : FiniteDimensional (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) :=
    Module.finite_of_finrank_pos
      (by rw [finrank_adjoin_jqN_eq_dedekindPsi]; exact dedekindPsi_pos N (NeZero.ne N))
  have h := IsIntegral.of_finite (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
    (AdjoinSimple.gen (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N))
  rwa [isIntegral_iff, AdjoinSimple.coe_gen] at h

theorem natDegree_minpoly_jqN (N : ℕ) [NeZero N] :
    (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).natDegree =
      dedekindPsi N := by
  rw [← adjoin.finrank (isIntegral_jqN N), finrank_adjoin_jqN_eq_dedekindPsi]

noncomputable def thetaE :
    (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* K⟮coeffEmb K jq⟯ :=
  ((coeffEmb K).comp
      (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (LaurentSeries ℚ))).codRestrict K⟮coeffEmb K jq⟯ fun y => by
    have h := coeffEmb_mem_laurentBaseChange K y.2
    rwa [laurentBaseChange_adjoin, Set.image_singleton] at h

theorem minpoly_coeffEmb_jqN (N : ℕ) [NeZero N] :
    IsIntegral K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N)) ∧
    minpoly K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N)) =
      (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map
        (thetaE K) := by
  have hpm : (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).Monic :=
    minpoly.monic (isIntegral_jqN N)
  have heval : aeval (coeffEmb K (jqN N))
      ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN N)).map
        (thetaE K)) = 0 := by
    rw [aeval_def, eval₂_map,
      show (algebraMap K⟮coeffEmb K jq⟯ (LaurentSeries K)).comp (thetaE K) =
          (coeffEmb K).comp
            (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
              (LaurentSeries ℚ)) from RingHom.ext fun _ => rfl,
      ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hint : IsIntegral K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N)) :=
    ⟨_, hpm.map _, by rwa [← aeval_def]⟩
  refine ⟨hint, (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (hpm.map _)
    (minpoly.dvd _ _ heval) (le_of_eq ?_)).symm⟩
  rw [hpm.natDegree_map, natDegree_minpoly_jqN, ← adjoin.finrank hint, finrank_adjoin_adjoin]

theorem eval₂_minpoly_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    (minpoly K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N))).eval₂
        ((qExpand K N).comp (algebraMap K⟮coeffEmb K jq⟯ (LaurentSeries K)))
        (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) = 0 := by
  rw [(minpoly_coeffEmb_jqN K N).2, eval₂_map,
    show ((qExpand K N).comp (algebraMap K⟮coeffEmb K jq⟯ (LaurentSeries K))).comp (thetaE K) =
        ((coeffEmb K).comp (qExpand ℚ N)).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)) from RingHom.ext fun y => by
      show qExpand K N (coeffEmb K (y : LaurentSeries ℚ)) =
        coeffEmb K (qExpand ℚ N (y : LaurentSeries ℚ))
      exact qExpand_coeffEmb K N _,
    ← eval_map,
    minpoly_jqN_map_eq_prod_slots N ζ hζ
      (fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩),
    eval_prod]
  refine Finset.prod_eq_zero (Nat.mem_divisors.mpr ⟨ha, NeZero.ne N⟩) ?_
  rw [eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hg⟩) ?_
  simp only [eval_sub, eval_X, eval_C, dif_neg (NeZero.ne a), sub_self]

private theorem _root_.ModularCurve.exists_algHom_laurentBaseChange_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    ∃ ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K,
      ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) := by
  obtain ⟨hint, -⟩ := minpoly_coeffEmb_jqN K N

  let L := AdjoinRoot.lift ((qExpand K N).comp (algebraMap K⟮coeffEmb K jq⟯ (LaurentSeries K)))
    (qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (eval₂_minpoly_slot K N ζ hζ a b ha hb hg)
  let e := adjoinRootEquivAdjoin K⟮coeffEmb K jq⟯ hint
  let φ : K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯ →+* LaurentSeries K :=
    L.comp (e.symm : K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯ →+*
      AdjoinRoot (minpoly K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N))))
  have hφalg : ∀ x : K⟮coeffEmb K jq⟯,
      φ (algebraMap K⟮coeffEmb K jq⟯ K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯ x) =
        qExpand K N x := fun x => by
    show L (e.symm (algebraMap _ _ x)) = _
    rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hφgen : φ (AdjoinSimple.gen K⟮coeffEmb K jq⟯ (coeffEmb K (jqN N))) =
      qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) := by
    show L (e.symm (AdjoinSimple.gen _ _)) = _
    rw [adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]
  have hF := laurentBaseChange_full_eq_adjoin_adjoin K N

  let ι' : (K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯).restrictScalars K →ₐ[K] LaurentSeries K :=
    { toRingHom := φ
      commutes' := fun c => by
        show φ (algebraMap K⟮coeffEmb K jq⟯ K⟮coeffEmb K jq⟯⟮coeffEmb K (jqN N)⟯
          (algebraMap K K⟮coeffEmb K jq⟯ c)) = _
        rw [hφalg]
        show qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }
  refine ⟨ι'.comp (inclusion hF.le), ?_, ?_⟩
  · exact hφalg ⟨coeffEmb K jq, mem_adjoin_simple_self K _⟩
  · exact hφgen

p2m_alias "P2MW.S_ModularCurve_exists_algHom_laurentBaseChange_slot.ModularCurve.exists_algHom_laurentBaseChange_slot" "ModularCurve.exists_algHom_laurentBaseChange_slot"
end CD

open ModularCurve AlgebraicCurve in

theorem solution (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    ∃ ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K,
      ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) :=
  ModularCurve.exists_algHom_laurentBaseChange_slot K N ζ hζ a b ha hb hg

#print axioms solution

end S_ModularCurve_exists_algHom_laurentBaseChange_slot
end P2MW
export P2MW.S_ModularCurve_exists_algHom_laurentBaseChange_slot (solution)
