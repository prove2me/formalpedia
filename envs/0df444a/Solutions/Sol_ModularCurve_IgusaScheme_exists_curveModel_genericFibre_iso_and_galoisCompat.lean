-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_curveModel_genericFibre_iso_and_galoisCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fbd2026d-5a7a-56e3-bea7-bc1f5c520462

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_isCurveOver_iff_exists_transcendental_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_IgusaScheme_exists_genericFibre_iso_ofGenerator_jBar_and_galoisCompat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

open ModularCurve ModularCurve.IgusaScheme ModularCurve.CharPModel
open AlgebraicCurve AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (eη : Mη.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (igusaTo N ℓ) _ = Mη.toBase ∧
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x := by

  have htrans : Transcendental (AlgebraicClosure ℚ) (jBar N) := by
    have hjq : Transcendental (AlgebraicClosure ℚ)
        ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
      have h := transcendental_jqModC (AlgebraicClosure ℚ)
      have hcoe : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
          = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq (AlgebraicClosure ℚ)
      exact hcoe ▸ h
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (modularFunctionFieldBar N)
        (LaurentSeries (AlgebraicClosure ℚ)))).mp hjq
  haveI hne : Fact (jBar N ≠ 0) := ⟨fun h => htrans (h ▸ isAlgebraic_zero)⟩
  haveI heft : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  have hco : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  obtain ⟨t, _, ht_fd, _⟩ :=
    isCurveOver_iff_exists_transcendental_finiteDimensional.mp hco
  haveI := ht_fd
  haveI hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_of_transcendental t htrans
  have htinv : Transcendental (AlgebraicClosure ℚ) ((jBar N)⁻¹) :=
    fun halg => htrans (by have h := halg.inv; rwa [inv_inv] at h)
  haveI hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_of_transcendental t htinv

  exact ⟨CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans,
    exists_genericFibre_iso_ofGenerator_jBar_and_galoisCompat N ℓ hℓN htrans⟩

end
end S_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat (solution)
