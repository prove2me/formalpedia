-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_pow_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f912bbb5-e73e-5b3b-a888-7b288c64b40a

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import Theorems.Thm_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_pow_eq_qExpansion
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "UpperHalfPlane ModularCurve~coeffEmb_jq"
open scoped MatrixGroups

noncomputable section

namespace P2bWeight

theorem thetaL_coeff {L : Type*} [Field L] (x : LaurentSeries L) (n : ℤ) :
    (thetaL L x).coeff n = (n : L) * x.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  simp only [Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem support_thetaL_subset {L : Type*} [Field L] (x : LaurentSeries L) :
    (thetaL L x).support ⊆ x.support := by
  intro n hn
  rw [HahnSeries.mem_support, thetaL_coeff] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

theorem thetaL_mul {L : Type*} [Field L] (x y : LaurentSeries L) :
    thetaL L (x * y) = thetaL L x * y + x * thetaL L y := by
  ext n
  rw [HahnSeries.coeff_add, thetaL_coeff,
    HahnSeries.coeff_mul_left' x.isPWO_support (support_thetaL_subset x),
    HahnSeries.coeff_mul_right' y.isPWO_support (support_thetaL_subset y),
    HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thetaL_coeff, thetaL_coeff, ← hij.2.2, Int.cast_add]
  ring

theorem thetaL_C {L : Type*} [Field L] (r : L) : thetaL L (HahnSeries.C r) = 0 := by
  ext n
  rw [thetaL_coeff, HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_zero]
  split_ifs with hn
  · rw [hn, Int.cast_zero, zero_mul]
  · exact mul_zero _

theorem thetaL_coe {L : Type*} [Field L] (p : PowerSeries L) :
    thetaL L (p : LaurentSeries L) =
      ((PowerSeries.mk fun n : ℕ => (n : L) * PowerSeries.coeff n p : PowerSeries L) :
        LaurentSeries L) := by
  ext n
  rw [thetaL_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · exact mul_zero _
  · rw [PowerSeries.coeff_mk]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h)
    simp

local notation "𝓔₄" =>
  ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
local notation "𝓔₆" =>
  ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
local notation "𝓓" =>
  ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem ofNat_laurent_ne_zero (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : LaurentSeries ℂ) ≠ 0 := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) n]
  exact HahnSeries.C_ne_zero (OfNat.ofNat_ne_zero n)

theorem D_ne_zero : 𝓓 ≠ 0 := by
  intro h
  have h1 := ModularForm.discriminant_qExpansion_coeff_one
  have h0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem E4_ne_zero : 𝓔₄ ≠ 0 := by
  intro h
  have h1 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  have h0 : qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem E6_ne_zero : 𝓔₆ ≠ 0 := by
  intro h
  have h1 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  have h0 : qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem discr_laurent : 1728 * 𝓓 = 𝓔₄ ^ 3 - 𝓔₆ ^ 2 := by
  have hfun : (1728 : ℂ) • (ModularForm.discriminant : ℍ → ℂ) =
      ⇑(ModularForm.E₄.pow 3) - ⇑(ModularForm.E₆.pow 2) := by
    ext z
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  have hps : (1728 : ℂ) • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) =
      qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) ^ 3 - qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) ^ 2 := by
    rw [← CuspForm.coe_discriminant,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, CuspForm.coe_discriminant,
      hfun, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hL := congrArg ((↑) : PowerSeries ℂ → LaurentSeries ℂ) hps
  simp only [PowerSeries.coe_smul, PowerSeries.coe_sub, PowerSeries.coe_pow] at hL
  rw [← HahnSeries.C_mul_eq_smul, map_ofNat] at hL
  exact hL

theorem rankinCohen_laurent :
    4 * 𝓔₄ * thetaL ℂ 𝓔₆ - 6 * thetaL ℂ 𝓔₄ * 𝓔₆ = -3456 * 𝓓 := by
  have hT : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ :=
    (MonoidHom.range_eq_map _).symm
  have h1 : (1 : ℝ) ∈ ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [hT]; exact one_mem_strictPeriods_SL
  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq h1
    (ModularForm.E₄.mcast rfl hT) (ModularForm.E₆.mcast rfl hT)
  simp only [ModularForm.coe_mcast, Int.cast_ofNat] at hB
  set B' : ModularForm 𝒮ℒ 12 := B.mcast (by norm_num) hT.symm with hB'def
  have hBB' : (B' : ℍ → ℂ) = B := rfl
  have h0 : (qExpansion 1 (B' : ℍ → ℂ)).coeff 0 = 0 := by
    rw [hBB', hB]
    simp
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm B' h0)
  have hcfun : (B : ℍ → ℂ) = c • ⇑CuspForm.discriminant := by
    rw [← CuspForm.IsGLPos.coe_smul, hc]; rfl
  have hqB : qExpansion 1 (B : ℍ → ℂ) =
      c • qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
    rw [hcfun, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      CuspForm.coe_discriminant]
  have hkey := hB.symm.trans hqB
  have hc1 : c = -3456 := by
    have h := congrArg (PowerSeries.coeff 1) hkey
    norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, PowerSeries.coeff_mk,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      ModularForm.E₄_qExpansion_coeff_one, ModularForm.E₆_qExpansion_coeff_one,
      ModularForm.discriminant_qExpansion_coeff_one] at h
    exact h.symm
  rw [hc1] at hkey
  have hL := congrArg ((↑) : PowerSeries ℂ → LaurentSeries ℂ) hkey
  rw [thetaL_coe, thetaL_coe]
  simp only [PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_smul, map_ofNat] at hL
  rw [hL, ← HahnSeries.C_mul_eq_smul, map_neg, map_ofNat]

theorem coeffEmb_jq : coeffEmb ℂ jq = 𝓔₄ ^ 3 / 𝓓 := by
  rw [← ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant,
    ← map_jqModC (algebraMap ℚ ℂ), jqModC_rat]
  rfl

theorem thetaL_j_mul_D : thetaL ℂ (coeffEmb ℂ jq) * 𝓓 = -(𝓔₄ ^ 2 * 𝓔₆) := by
  have hD := D_ne_zero
  have hRC := rankinCohen_laurent
  have hΔ := discr_laurent
  have hj := coeffEmb_jq

  have hC : coeffEmb ℂ jq * 𝓓 = 𝓔₄ ^ 3 := by rw [hj, div_mul_cancel₀ _ hD]

  have hA := congrArg (thetaL ℂ) hC
  rw [thetaL_mul, pow_succ, thetaL_mul, pow_two, thetaL_mul] at hA
  have hB := congrArg (thetaL ℂ) hΔ
  rw [thetaL_mul, map_sub, pow_succ, thetaL_mul, pow_two, thetaL_mul, pow_two, thetaL_mul]
    at hB

  have hθ1728 : thetaL ℂ (1728 : LaurentSeries ℂ) = 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 1728]
    exact thetaL_C _
  rw [hθ1728, zero_mul, zero_add] at hB
  apply mul_right_cancel₀ (mul_ne_zero (ofNat_laurent_ne_zero 3456) hD)
  linear_combination (3456 * 𝓓) * hA - (2 * coeffEmb ℂ jq * 𝓓) * hB
    - (2 * (3 * 𝓔₄ ^ 2 * thetaL ℂ 𝓔₄ - 2 * 𝓔₆ * thetaL ℂ 𝓔₆)) * hC
    + (6 * 𝓔₄ ^ 2 * thetaL ℂ 𝓔₄) * hΔ + (𝓔₄ ^ 2 * 𝓔₆) * hRC

end P2bWeight

open P2bWeight in

theorem p2bMain (N : ℕ) [NeZero N] (m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) ^ m =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({coeffEmb ℂ jq} : Set (LaurentSeries ℂ)))
      (Y ^ 6 * coeffEmb ℂ jq ^ (4 * m) * (coeffEmb ℂ jq - 1728) ^ (3 * m)) := by

  set e4 := ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with he4
  set e6 := ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with he6
  set d := ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    with hd
  set F := ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hF
  have hD : d ≠ 0 := D_ne_zero
  have h4 : e4 ≠ 0 := E4_ne_zero
  have h6 : e6 ≠ 0 := E6_ne_zero
  have hj : coeffEmb ℂ jq = e4 ^ 3 / d := coeffEmb_jq
  have hθ : thetaL ℂ (coeffEmb ℂ jq) * d = -(e4 ^ 2 * e6) := thetaL_j_mul_D
  have hΔ : 1728 * d = e4 ^ 3 - e6 ^ 2 := discr_laurent
  have hθv : thetaL ℂ (coeffEmb ℂ jq) = -(e4 ^ 2 * e6) / d := by
    rw [eq_div_iff hD]; exact hθ
  have hJ' : coeffEmb ℂ jq - 1728 = e6 ^ 2 / d := by
    rw [hj, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    linear_combination -hΔ

  have K1 : coeffEmb ℂ jq ^ 4 * (coeffEmb ℂ jq - 1728) ^ 3 * d = thetaL ℂ (coeffEmb ℂ jq) ^ 6 := by
    rw [hθv, hJ', hj]
    field_simp

  have helper : ∀ (Yx Jx Kx dx Tx : LaurentSeries ℂ), Jx ^ 4 * Kx ^ 3 * dx = Tx ^ 6 →
      (Yx ^ 6 * Jx ^ (4 * m) * Kx ^ (3 * m)) * dx ^ m = (Yx * Tx ^ m) ^ 6 := by
    intro Yx Jx Kx dx Tx h
    calc (Yx ^ 6 * Jx ^ (4 * m) * Kx ^ (3 * m)) * dx ^ m = Yx ^ 6 * (Jx ^ 4 * Kx ^ 3 * dx) ^ m := by ring
      _ = Yx ^ 6 * (Tx ^ 6) ^ m := by rw [h]
      _ = (Yx * Tx ^ m) ^ 6 := by ring

  have hEq : Y ^ 6 * coeffEmb ℂ jq ^ (4 * m) * (coeffEmb ℂ jq - 1728) ^ (3 * m) = F ^ 6 / d ^ m := by
    rw [eq_div_iff (pow_ne_zero _ hD), helper _ _ _ _ _ K1, hY]

  have h1N : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1
  set fM : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)) :=
    ModularFormClass.modularForm f with hfM
  set F6 : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (12 * (m : ℤ)) :=
    (fM.pow 6).mcast (by push_cast; ring) with hF6
  have hF6q : qExpansion 1 (F6 : ℍ → ℂ) = (qExpansion 1 (f : ℍ → ℂ)) ^ 6 := by
    show qExpansion 1 ⇑(fM.pow 6) = _
    rw [ModularForm.qExpansion_pow one_pos h1N]
    rfl
  have hF6L : ((qExpansion 1 (F6 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = F ^ 6 := by
    rw [hF6q, PowerSeries.coe_pow]
  have hI := ModularForm.isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic
    (𝒢 := (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) h1N m (k := 12 * (m : ℤ))
    rfl F6
  rw [hF6L] at hI
  rw [hEq, hj]
  exact hI

end

theorem solution (N : ℕ) [NeZero N] (m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (Y : LaurentSeries ℂ)
    (hY : Y * thetaL ℂ (coeffEmb ℂ jq) ^ m =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({coeffEmb ℂ jq} : Set (LaurentSeries ℂ)))
      (Y ^ 6 * coeffEmb ℂ jq ^ (4 * m) * (coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)) := by
  rw [map_ofNat]
  exact p2bMain N m f Y hY

end S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_pow_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_pow_eq_qExpansion (solution)
