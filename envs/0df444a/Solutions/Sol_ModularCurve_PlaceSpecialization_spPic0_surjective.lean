-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.spPic0_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ca20b43a-f222-506d-8638-552bf6a65f2b

import Definitions.Def_ModularCurve_PlaceSpecialization
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_surjective
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open AlgebraicCurve ModularCurve

theorem solution {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] (S : PlaceSpecialization A ℓ N data hKr k red hα hβ) :
    Function.Surjective S.spPic0 := by
  intro y
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective y
  have hss : S.sp ∘ Function.surjInv S.d4 = id := funext fun v' => Function.surjInv_eq S.d4 v'
  have hmap : Finsupp.mapDomain S.sp
      (Finsupp.mapDomain (Function.surjInv S.d4) (D' : Divisor k (modularFunctionFieldC k N)))
        = (D' : Divisor k (modularFunctionFieldC k N)) := by
    rw [← Finsupp.mapDomain_comp, hss, Finsupp.mapDomain_id]
  have hdeg : Finsupp.mapDomain (Function.surjInv S.d4) (D' : Divisor k (modularFunctionFieldC k N))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) := by
    rw [Divisor.mem_degZero]
    have h' : Divisor.degree (D' : Divisor k (modularFunctionFieldC k N)) = 0 := D'.2
    simp only [Divisor.degree, Finsupp.liftAddHom_apply] at h' ⊢
    rw [Finsupp.sum_mapDomain_index_addMonoidHom]
    simp only [Finsupp.sum, AddMonoidHom.mulRight_apply, deg_eq_one_modularFunctionFieldBar,
      Nat.cast_one, mul_one]
    simp only [Finsupp.sum, AddMonoidHom.mulRight_apply, place_deg_eq_one_of_isAlgClosed,
      Nat.cast_one, mul_one] at h'
    exact h'
  refine ⟨Pic0.mk ⟨_, hdeg⟩, ?_⟩
  obtain ⟨D₁, hD₁, h₁⟩ := S.spPic0_compat ⟨_, hdeg⟩
  rw [h₁]
  congr 1
  exact Subtype.ext (by rw [hD₁]; exact hmap)

end S_ModularCurve_PlaceSpecialization_spPic0_surjective
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_spPic0_surjective (solution)
