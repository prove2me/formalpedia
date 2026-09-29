-- Prove2me | solution 1 for ModularCurve.diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/db923123-6be2-5c75-8fdc-a627899daa74

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_xHFunctionField_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField

namespace DiamondFixX0

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

set_option synthInstance.maxHeartbeats 1600000 in
theorem isBaseChangeAutOf_unique {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {σ σ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ σ) (h' : IsBaseChangeAutOf L σ₀ σ') : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  have hx' : x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      apply Subtype.ext
      exact (h ⟨z, hz⟩).trans (h' ⟨z, hz⟩).symm
  | algebraMap c =>
      have : (⟨algebraMap L (LaurentSeries L) c, IntermediateField.algebraMap_mem _ c⟩ :
          laurentBaseChange L F₀) = algebraMap L (laurentBaseChange L F₀) c := rfl
      rw [this, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have : (⟨y + z, add_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [this, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have : (⟨y⁻¹, inv_mem hy⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have : (⟨y * z, mul_mem hy hz⟩ : laurentBaseChange L F₀) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [this, map_mul, map_mul, ihy, ihz]

variable (L) [Algebra.IsAlgebraic ℚ L]

set_option synthInstance.maxHeartbeats 1600000 in
theorem baseChangeAut_eq_geomAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    baseChangeAut L σ₀ = geomAut L F₀ σ₀ := by
  have hgeom : IsBaseChangeAutOf L σ₀ (geomAut L F₀ σ₀) := fun y =>
    coe_geomAut_coeffEmb L F₀ σ₀ y
  exact isBaseChangeAutOf_unique (isBaseChangeAutOf_baseChangeAut ⟨_, hgeom⟩) hgeom

set_option synthInstance.maxHeartbeats 1600000 in
theorem diamondAutBar_eq_geomAut (N d : ℕ) :
    diamondAutBar N d = geomAut (AlgebraicClosure ℚ) (x1FunctionField N) (diamondAut N d) :=
  baseChangeAut_eq_geomAut (AlgebraicClosure ℚ) (diamondAut N d)

end BaseChange

set_option synthInstance.maxHeartbeats 1600000 in
theorem isDiamondAut_iff_mod (N : ℕ) [NeZero N] (d : ℕ) (σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N) :
    IsDiamondAut N d σ ↔ IsDiamondAut N (d % N) σ := by
  have hcop : Nat.Coprime d N ↔ Nat.Coprime (d % N) N := by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm d N, Nat.gcd_rec N d]
  have hcast : ((d % N : ℕ) : ZMod N) = (d : ZMod N) := ZMod.natCast_mod d N
  unfold IsDiamondAut
  rw [hcop, hcast]

set_option synthInstance.maxHeartbeats 1600000 in
theorem diamondAut_mod (N : ℕ) [NeZero N] (d : ℕ) : diamondAut N d = diamondAut N (d % N) := by
  have hP : IsDiamondAut N d = IsDiamondAut N (d % N) :=
    funext fun σ => propext (isDiamondAut_iff_mod N d σ)
  unfold diamondAut
  rw [hP]

end DiamondFixX0

end

open ModularCurve DiamondFixX0 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (c : ℕ)
    (f : ↥(ModularCurve.modularFunctionFieldFull N))
    (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar N) :
    ModularCurve.diamondAutBar N c ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ =
      ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ := by
  classical

  have hF : ModularCurve.xHFunctionField N ⊤ = ModularCurve.modularFunctionFieldFull N := by
    rw [← ModularCurve.xHFunctionFieldC_rat, ModularCurve.xHFunctionFieldC_top,
      ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  have hle : ModularCurve.modularFunctionFieldFull N ≤ ModularCurve.x1FunctionField N := by
    rw [← hF]
    exact ModularCurve.xHFunctionFieldC_le_x1 ℚ N ⊤
  set x : ↥(ModularCurve.x1FunctionField N) := ⟨(f : LaurentSeries ℚ), hle f.2⟩ with hx

  have hfix : diamondAut N c x = x := by
    by_cases hc : Nat.Coprime c N
    · obtain ⟨δ, hδ, hgal⟩ := ModularCurve.exists_monoidHom_diamondAut_mem_xHFunctionField_iff N ⊤
        (fun d hd => ModularCurve.exists_isDiamondAut N hd)
      let u : (⊤ : Subgroup (ZMod N)ˣ) := ⟨ZMod.unitOfCoprime c hc, trivial⟩
      have hxmem : (x : LaurentSeries ℚ) ∈ ModularCurve.xHFunctionField N ⊤ := by
        rw [hF]; exact f.2
      have h1 := (hgal x).mp hxmem u
      rw [hδ u] at h1
      have hval : (((u : (ZMod N)ˣ) : ZMod N)).val = c % N := by
        show ((ZMod.unitOfCoprime c hc : (ZMod N)ˣ) : ZMod N).val = c % N
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      rw [hval, ← diamondAut_mod] at h1
      exact h1
    · rw [diamondAut_of_not_coprime hc]
      rfl

  have key := geomAut_coeffEmb (AlgebraicClosure ℚ) (x1FunctionField N) (diamondAut N c) x
  rw [hfix] at key
  have hy : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ : ↥(ModularCurve.x1FunctionFieldBar N)) =
      ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := rfl
  rw [hy, diamondAutBar_eq_geomAut]
  exact key

end S_ModularCurve_diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq
end P2MW
export P2MW.S_ModularCurve_diamondAutBar_apply_coeffEmb_modularFunctionFieldFull_eq (solution)
