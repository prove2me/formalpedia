-- Prove2me | solution 1 for ModularCurve.FullLevel.levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e6fdbceb-ee3f-5c0d-ae8a-0197a19cdc23

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open scoped MatrixGroups

namespace TauSwapAux

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq~coeffEmb_qExpand~coeffMap_injective"

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases h : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ h, qExpand_coeff_of_not_dvd N _ h, map_zero]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_mem_laurentBaseChange' {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra ℚ L₁] [Algebra ℚ L₂]
    (σ : L₁ →+* L₂) (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L₁}
    (hx : x ∈ laurentBaseChange L₁ F₀) : coeffMap σ x ∈ laurentBaseChange L₂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L₂ F₀).algebraMap_mem _
      · rw [coeffEmb, coeffMap_coeffMap, coeffMap_congr (RingHom.ext_rat (σ.comp (algebraMap ℚ L₁)) (algebraMap ℚ L₂))]
        exact coeffEmb_mem_laurentBaseChange L₂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  show (jqModC ℚ).map (algebraMap ℚ L) = jqModC L
  exact map_jqModC (algebraMap ℚ L)

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ N x) = qExpand L N (coeffEmb L x) :=
  coeffMap_qExpand (algebraMap ℚ L) N x

theorem coeffEmb_qExpand_jq_mem (L : Type*) [Field L] [Algebra ℚ L] (M' : ℕ) [NeZero M'] (d : ℕ) [NeZero d]
    (hd : d ∣ M') :
    coeffEmb L (qExpand ℚ d jq) ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
  rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full M' hd)

end TauSwapAux

p2m_open "P2MW.S_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom.TauSwapAux ModularCurve~coeffMap_qExpand~coeffEmb_jq~coeffEmb_qExpand~coeffMap_injective ModularCurve.FullLevel"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M' : ¬ ℓ' ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (e : L →+* AlgebraicClosure ℚ)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (γ : SL(2, ℤ)) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M') (hγℓ : γ ∈ CongruenceSubgroup.Gamma ℓ')
    (hγq : ((γ 0 0 : ℤ) : ZMod q) = 0 ∧ ((γ 1 1 : ℤ) : ZMod q) = 0)
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ)
    (d : ℕ) [NeZero d] (hd : d ∣ M') [NeZero (q * ℓ' * d)] [NeZero (q * q * ℓ' * d)]
    (hbK : ModularCurve.qExpand L ℓ' (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq)) ∈ K)
    (hbPK : ModularCurve.jqNModC L (q * q * ℓ' * d) ∈ K)
    (hcK : ModularCurve.jqNModC L (q * ℓ' * d) ∈ K) :
    τ ⟨_, hbK⟩ = ⟨_, hbPK⟩ ∧ τ ⟨_, hcK⟩ = ⟨_, hcK⟩ := by
  classical
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ'.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero ℓ' := ⟨hℓp.ne_zero⟩
  haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hqp.ne_zero⟩
  haveI : NeZero (q * ℓ') := ⟨mul_ne_zero hqp.ne_zero hℓp.ne_zero⟩
  haveI : NeZero (ℓ' * q ^ 2) := ⟨mul_ne_zero hℓp.ne_zero (pow_ne_zero 2 hqp.ne_zero)⟩

  set Kq : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) with hKq
  have hζ : IsPrimitiveRoot (ξ ^ ℓ') q := hξ.pow (Nat.pos_of_ne_zero (mul_ne_zero hqp.ne_zero hℓp.ne_zero)) (mul_comm q ℓ')
  obtain ⟨τq, hτq⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0 q hq M' hqM' L (ξ ^ ℓ') hζ Kq hKq γ hγ0

  have hxb : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq) ∈ Kq := by
    have h := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull L M' 1
      (q ^ 2 * M') ⟨q ^ 2, by ring⟩ (ModularCurve.FullLevel.levelH q M') (ModularCurve.qExpand ℚ d ModularCurve.jq)
      (jqd_mem_full M' hd)
    rwa [qExpand_one_apply, ← hKq] at h
  refine ⟨?_, ?_⟩
  ·

    have hres := ModularCurve.FullLevel.AuxLevel.coe_apply_eq_qExpand_coe_apply_of_isLevelAutAt_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L ξ hξ hι K hK Kq hKq γ hγ0 τ hτ τq hτq ⟨_, hxb⟩ ⟨_, hbK⟩ rfl

    set ζ' : ModularCurve.FullLevel.Idx q := ModularCurve.FullLevel.Idx.mk (e (ξ ^ ℓ')) (hζ.map_of_injective e.injective) with hζ'def
    have hζ' : ζ'.val = e (ξ ^ ℓ') := rfl
    have hιq : ∃ ι : L →+* ℂ, ι (ξ ^ ℓ') = Complex.exp (2 * Real.pi * Complex.I / q) := by
      obtain ⟨ι, hι⟩ := hι
      refine ⟨ι, ?_⟩
      rw [map_pow, hι, ← Complex.exp_nat_mul]
      congr 1
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hqp.ne_zero
      have hℓ0 : (ℓ' : ℂ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
      field_simp
    let ιK : ↥Kq →+* ↥(ModularCurve.FullLevel.fieldBar q M') :=
      { toFun := fun x => ⟨ModularCurve.coeffMap e (x : LaurentSeries L),
          coeffMap_mem_laurentBaseChange' e _ (by rw [← hKq]; exact x.2)⟩
        map_one' := by ext : 1; simp
        map_mul' := fun x y => by ext : 1; simp
        map_zero' := by ext : 1; simp
        map_add' := fun x y => by ext : 1; simp }
    have hιK : ∀ x : ↥Kq, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap e (x : LaurentSeries L) := fun x => rfl
    have hγinv : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ0
    have hbar := ModularCurve.FullLevel.levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap q hq M' hqM' L (ξ ^ ℓ') hζ hιq
      Kq hKq e ζ' hζ' ιK hιK γ⁻¹ hγinv τq hτq ⟨_, hxb⟩

    have ha : (q : ℤ) ∣ ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hγq.2
    have hg : ModularCurve.coeffMap e (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq)) =
        ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq) := by
      rw [ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap,
        ModularCurve.coeffMap_congr (RingHom.ext_rat (e.comp (algebraMap ℚ L)) (algebraMap ℚ (AlgebraicClosure ℚ)))]
      rfl
    have hswap := ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ'
      γ⁻¹ hγinv ha (ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq))
      (coeffEmb_qExpand_jq_mem (AlgebraicClosure ℚ) M' d hd) (ιK ⟨_, hxb⟩) (by rw [hιK]; exact hg)

    have hτq : ((τq ⟨_, hxb⟩ : ↥Kq) : LaurentSeries L) =
        ModularCurve.qExpand L (q ^ 2) (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq)) := by
      apply coeffMap_injective e e.injective
      rw [← hιK, hbar, hswap, coeffMap_qExpand, hg]

    apply Subtype.ext
    show ((τ ⟨_, hbK⟩ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * q * ℓ' * d)
    rw [hres, hτq, coeffEmb_qExpand, coeffEmb_jq, ModularCurve.qExpand_qExpand, ModularCurve.qExpand_qExpand,
      ModularCurve.jqNModC]
    exact ModularCurve.qExpand_congr (by ring) _
  ·
    have hfix := (ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L ξ hξ hι K hK).2 ⟨_, hcK⟩
    refine (hfix.mpr ⟨ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq),
      coeffEmb_qExpand_jq_mem L M' d hd, ?_⟩) γ hγ0 τ hτ
    show ModularCurve.jqNModC L (q * ℓ' * d) =
      ModularCurve.qExpand L (q * ℓ') (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ d ModularCurve.jq))
    rw [coeffEmb_qExpand, coeffEmb_jq, ModularCurve.qExpand_qExpand, ModularCurve.jqNModC]

end S_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom
end P2MW
export P2MW.S_ModularCurve_FullLevel_levelAut_apply_qExpand_jq_eq_jqNModC_of_antidiagonal_of_ringHom (solution)
