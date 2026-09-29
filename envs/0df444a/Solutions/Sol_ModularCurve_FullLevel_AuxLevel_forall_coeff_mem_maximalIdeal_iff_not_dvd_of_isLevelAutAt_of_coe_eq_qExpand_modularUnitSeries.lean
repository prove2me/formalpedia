-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a57e22d2-ced0-5693-ad83-2cae15d4c055

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_CohCarrier_Level

import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv
import Theorems.Thm_LaurentSeries_forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom
import Theorems.Thm_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (x : ↥K) (hx : ((x : ↥K) : LaurentSeries L) =
      ModularCurve.qExpand L (q * ℓ) (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)))
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K τ) :
    (∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((τ x : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ↔
      ¬ ((q : ℤ) ∣ (δ 1 0 : ℤ)) := by
  classical
  haveI hq0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI hℓ0 : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  obtain ⟨huniqA, hmul, hone⟩ :=
    ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hex := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have h11 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') 1 K 1 := hone 1 (one_mem _) (one_mem _)

  have hT0 : ∀ s : ℤ, ModularGroup.T ^ s ∈ CongruenceSubgroup.Gamma0 M' := by
    intro s
    rw [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T_zpow]
    simp

  have hlead : ((x : ↥K) : LaurentSeries L).coeff (((q * ℓ : ℕ) : ℤ) * (1 - (q : ℤ))) = 1 := by
    rw [hx, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffEmb_coeff, ModularCurve.coeff_modularUnitSeries_self, map_one]
  constructor
  ·
    intro hG hdvd
    have hfix := ModularCurve.FullLevel.AuxLevel.apply_eq_self_of_isLevelAutAt_of_dvd_of_coe_eq_qExpand_modularUnitSeries q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA x hx δ hδ τ hτ hdvd
    obtain ⟨mm, hmm, hcoef⟩ := hG (((q * ℓ : ℕ) : ℤ) * (1 - (q : ℤ)))
    rw [hfix, hlead] at hcoef
    have h1 : mm = 1 := hinjAL (by rw [← hcoef, map_one])
    rw [h1] at hmm
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hmm)
  ·
    intro hndvd

    have hqprime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hqprime).mpr hndvd

    set s : ℤ := -(b * (δ 0 0 : ℤ)) with hsdef
    have hs : (q : ℤ) ∣ (δ 0 0 : ℤ) + s * (δ 1 0 : ℤ) := by
      refine ⟨a * (δ 0 0 : ℤ), ?_⟩
      have : (δ 0 0 : ℤ) = (a * (q : ℤ) + b * (δ 1 0 : ℤ)) * (δ 0 0 : ℤ) := by rw [hab, one_mul]
      rw [hsdef]; linear_combination this
    set δ' : SL(2, ℤ) := ModularGroup.T ^ s * δ with hδ'def
    have hδ'0 : δ' ∈ CongruenceSubgroup.Gamma0 M' := mul_mem (hT0 s) hδ
    have hδ'00 : (q : ℤ) ∣ (δ' 0 0 : ℤ) := by
      have : (δ' 0 0 : ℤ) = (δ 0 0 : ℤ) + s * (δ 1 0 : ℤ) := by
        rw [hδ'def, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]; exact hs

    obtain ⟨σ, hσ⟩ := hex (ModularGroup.T ^ s) (hT0 s)
    obtain ⟨σ', hσ'⟩ := hex (ModularGroup.T ^ s)⁻¹ (inv_mem (hT0 s))
    have hσσ' : σ * σ' = 1 := by
      have h := hmul _ _ (inv_mem (hT0 s)) (inv_mem (inv_mem (hT0 s))) _ _ hσ hσ'
      rw [inv_inv, mul_inv_cancel] at h
      exact huniqA 1 (one_mem _) _ _ h h11
    have hσ'σ : σ' * σ = 1 := by
      have h := hmul _ _ (inv_mem (inv_mem (hT0 s))) (inv_mem (hT0 s)) _ _ hσ' hσ
      rw [inv_inv, inv_mul_cancel] at h
      exact huniqA 1 (one_mem _) _ _ h h11
    have hσ'' : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (ModularGroup.T ^ (-s))⁻¹ K σ' := by
      rw [zpow_neg]; exact hσ'

    have hτ' : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') δ'⁻¹ K (σ * τ) := by
      have h := hmul _ _ (inv_mem (hT0 s)) (inv_mem hδ) _ _ hσ hτ
      rw [hδ'def, mul_inv_rev]; exact h

    obtain ⟨hinc, -⟩ :=
      ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
    obtain ⟨-, hmemq, -, -⟩ :=
      ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd q (q ^ 2 * M')
        (ModularCurve.FullLevel.levelH q M') ⟨q * M', by ring⟩
    have hmemK : ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) ∈ K :=
      hinc _ (ModularCurve.coeffEmb_mem_laurentBaseChange L hmemq)
    set w : ↥K := ⟨_, hmemK⟩ with hwdef
    have hw : ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries q)) := rfl

    have hP2 := ModularCurve.FullLevel.AuxLevel.apply_mul_eq_pow_twelve_of_isLevelAutAt_of_dvd_apply_zero_zero_of_coe_eq_qExpand_modularUnitSeries q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA x hx δ' hδ'0 (σ * τ) hτ' hδ'00 w hw
    have hprod : τ x * σ' w = algebraMap L ↥K ((q : L) ^ 12) := by
      have := congrArg σ' hP2
      rw [map_mul, AlgEquiv.commutes, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply σ' σ, hσ'σ, AlgEquiv.one_apply] at this
      exact this

    obtain ⟨u, hu, htw⟩ := ModularCurve.FullLevel.AuxLevel.exists_isUnit_forall_coeff_apply_eq_pow_mul_coeff_of_isLevelAutAt_T_zpow_inv q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA (-s) σ' hσ''

    obtain ⟨⟨xi, hxi, hxi1, hxi0⟩, -, -, -⟩ :=
      ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd q q (⊤ : Subgroup (ZMod q)ˣ) (dvd_refl q)
    have hcoefQ : ∀ k : ℤ, (ModularCurve.modularUnitSeries q).coeff k = ((xi.coeff k : ℤ) : ℚ) := by
      intro k; rw [← hxi, ModularCurve.coeffMap_coeff]; rfl

    have hZcoef : ∀ n : ℤ, ((σ' w : ↥K) : LaurentSeries L).coeff n =
        (algebraMap A L u) ^ n * (if (ℓ : ℤ) ∣ n then algebraMap A L ((xi.coeff (n / ℓ) : ℤ) : A) else 0) := by
      intro n
      rw [htw w n, hw]
      congr 1
      split_ifs with hdn
      · obtain ⟨k, rfl⟩ := hdn
        rw [ModularCurve.qExpand_coeff_mul, ModularCurve.coeffEmb_coeff, hcoefQ,
          Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ))]
        simp
      · rw [ModularCurve.qExpand_coeff_of_not_dvd _ _ hdn]

    have huz' : ∀ n : ℤ, (algebraMap A L u) ^ n = algebraMap A L ((hu.unit ^ n : Aˣ) : A) := by
      intro n
      have h1 : algebraMap A L ((hu.unit ^ n : Aˣ) : A) =
          ((Units.map (algebraMap A L : A →* L) (hu.unit ^ n) : Lˣ) : L) := (Units.coe_map _ _).symm
      rw [h1, map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map, IsUnit.unit_spec]
      rfl
    have huz : ∀ n : ℤ, ∃ v : A, (algebraMap A L u) ^ n = algebraMap A L v :=
      fun n => ⟨_, huz' n⟩
    have hmain := LaurentSeries.forall_coeff_mem_map_maximalIdeal_of_mul_eq_C_of_forall_coeff_mem_range_of_isUnit_coeff_order A L hinjAL (IsLocalRing.maximalIdeal A)
      ((τ x : ↥K) : LaurentSeries L) ((σ' w : ↥K) : LaurentSeries L) ((ℓ : ℤ) * (1 - (q : ℤ))) ((q : A) ^ 12)
      (by
        intro n
        rw [hZcoef n]
        obtain ⟨v, hv⟩ := huz n
        split_ifs
        · exact ⟨v * ((xi.coeff (n / ℓ) : ℤ) : A), by rw [hv, map_mul]⟩
        · exact ⟨0, by simp⟩)
      (by
        intro n hn
        rw [hZcoef n]
        split_ifs with hdn
        · obtain ⟨k, rfl⟩ := hdn
          have hk : k < 1 - (q : ℤ) := by
            have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
            nlinarith
          rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ)), hxi0 k hk]
          simp
        · simp)
      (by
        obtain ⟨v, hv⟩ := huz ((ℓ : ℤ) * (1 - (q : ℤ)))
        refine ⟨((hu.unit ^ ((ℓ : ℤ) * (1 - (q : ℤ))) : Aˣ) : A), Units.isUnit _, ?_⟩
        rw [hZcoef, if_pos ⟨_, rfl⟩, Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne ℓ)), hxi1]
        simp only [Int.cast_one, map_one, mul_one]
        exact huz' _)
      (by
        have := congrArg (fun t : ↥K => ((t : ↥K) : LaurentSeries L)) hprod
        simp only [IntermediateField.coe_mul] at this
        rw [this]
        rw [show (((algebraMap L ↥K ((q : L) ^ 12)) : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) ((q : L) ^ 12) from rfl,
          ModularCurve.algebraMap_laurentSeries_eq_single]
        simp)
      (Ideal.pow_mem_of_mem _ hAq 12 (by norm_num))
    exact hmain

end S_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_coeff_mem_maximalIdeal_iff_not_dvd_of_isLevelAutAt_of_coe_eq_qExpand_modularUnitSeries (solution)
