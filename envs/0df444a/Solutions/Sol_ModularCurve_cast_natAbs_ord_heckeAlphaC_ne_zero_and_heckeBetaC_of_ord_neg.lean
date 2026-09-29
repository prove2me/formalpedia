-- Prove2me | solution 1 for ModularCurve.cast_natAbs_ord_heckeAlphaC_ne_zero_and_heckeBetaC_of_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/25c176fd-a584-5d74-be87-c0d8acaed5b7

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cast_natAbs_ord_heckeAlphaC_ne_zero_and_heckeBetaC_of_ord_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace CuspTameE4

theorem exists_place_of_eq {K L : Type*} [Field K] [Field L] [Algebra K L] {E₁ E₂ : IntermediateField K L}
    (h : E₁ = E₂) (y : AlgebraicCurve.Place K ↥E₁) :
    ∃ y' : AlgebraicCurve.Place K ↥E₂, ∀ (x : ↥E₁) (hx : (x : L) ∈ E₂), y'.ord ⟨x, hx⟩ = y.ord x := by
  subst h
  exact ⟨y, fun x hx => rfl⟩

end CuspTameE4

open CuspTameE4 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) (hy : y.ord (heckeAlphaC K N ℓ (jGeomGen K N)) < 0) :
    (((y.ord (heckeAlphaC K N ℓ (jGeomGen K N))).natAbs : ℕ) : K) ≠ 0 ∧
    (((y.ord (heckeBetaC K N ℓ (jGeomGen K N))).natAbs : ℕ) : K) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ.ne_zero⟩
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hpℓ : ¬ p ∣ ℓ := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
  have hpNℓ : ¬ p ∣ N * ℓ := fun h => (hp.dvd_mul.mp h).elim hpN hpℓ
  have hM : ((N * ℓ : ℕ) : K) ≠ 0 := fun h => hpNℓ ((CharP.cast_eq_zero_iff K p _).mp h)
  have hroof := ModularCurve.charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul K p N ℓ hpNℓ
  obtain ⟨w, hw⟩ := exists_place_of_eq hroof y

  have hαmem : ((heckeAlphaC K N ℓ (jGeomGen K N) : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K)
      ∈ modularFunctionFieldFullC K (N * ℓ) := by
    rw [coe_heckeAlphaC]; exact jqModC_mem_full K (N * ℓ)
  have hβmem : ((heckeBetaC K N ℓ (jGeomGen K N) : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K)
      ∈ modularFunctionFieldFullC K (N * ℓ) := by
    rw [coe_heckeBetaC]; exact jqModCd_mem_full K (N * ℓ) (dvd_mul_left ℓ N)
  have hα' : y.ord (heckeAlphaC K N ℓ (jGeomGen K N)) = w.ord ⟨_, hαmem⟩ := (hw _ hαmem).symm
  have hβ' : y.ord (heckeBetaC K N ℓ (jGeomGen K N)) = w.ord ⟨_, hβmem⟩ := (hw _ hβmem).symm
  have exα : (⟨_, hαmem⟩ : ↥(modularFunctionFieldFullC K (N * ℓ))) = ⟨jqModC K, jqModC_mem_full K (N * ℓ)⟩ :=
    Subtype.ext (coe_heckeAlphaC K N ℓ _)
  have exα1 : (⟨qExpand K 1 (jqModC K), jqModCd_mem_full K (N * ℓ) (one_dvd _)⟩ : ↥(modularFunctionFieldFullC K (N * ℓ)))
      = ⟨jqModC K, jqModC_mem_full K (N * ℓ)⟩ := Subtype.ext (qExpand_one_apply _)
  have exβ : (⟨_, hβmem⟩ : ↥(modularFunctionFieldFullC K (N * ℓ)))
      = ⟨qExpand K ℓ (jqModC K), jqModCd_mem_full K (N * ℓ) (dvd_mul_left ℓ N)⟩ :=
    Subtype.ext (coe_heckeBetaC K N ℓ _)
  rw [exα] at hα'
  rw [exβ] at hβ'
  have hwneg : w.ord ⟨jqModC K, jqModC_mem_full K (N * ℓ)⟩ < 0 := by
    have h := hy
    rwa [hα'] at h
  have k1 := ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg p K (N * ℓ) hM w hwneg 1 (one_dvd _)
  have kℓ := ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg p K (N * ℓ) hM w hwneg ℓ (dvd_mul_left ℓ N)
  rw [exα1] at k1
  refine ⟨?_, ?_⟩
  · rwa [hα']
  · rwa [hβ']

end S_ModularCurve_cast_natAbs_ord_heckeAlphaC_ne_zero_and_heckeBetaC_of_ord_neg
end P2MW
export P2MW.S_ModularCurve_cast_natAbs_ord_heckeAlphaC_ne_zero_and_heckeBetaC_of_ord_neg (solution)
