-- Prove2me | solution 1 for ModularCurve.three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c2e0f76a-cbfa-5631-99e7-7db10749904b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC

set_option autoImplicit false
set_option maxHeartbeats 16000000

open CongruenceSubgroup ModularCurve AlgebraicCurve ModularForm EisensteinSeries UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace DivTrivAux

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  unfold IsIntegralQExp
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk,
    eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) eisenstein6 := by
  unfold IsIntegralQExp
  ext n
  rw [PowerSeries.coeff_map, E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein6, PowerSeries.coeff_mk,
    eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

theorem eisenstein4_cube_sub_eisenstein6_sq :
    eisenstein4 ^ 3 - eisenstein6 ^ 2 = PowerSeries.C (1728 : ℤ) * (PowerSeries.X * dedekindEtaUnit) := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  have h4 : PowerSeries.map (Int.castRingHom ℂ) eisenstein4 = qExpansion 1 (E₄ : ℍ → ℂ) := isIntegralQExp_E4
  have h6 : PowerSeries.map (Int.castRingHom ℂ) eisenstein6 = qExpansion 1 (E₆ : ℍ → ℂ) := isIntegralQExp_E6
  rw [map_sub, map_pow, map_pow, h4, h6, map_mul, PowerSeries.map_C,
    ← ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, eq_intCast, Int.cast_ofNat]

  let F12 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)
  have hq : qExpansion 1 (F12 : ℍ → ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) ^ 3 - qExpansion 1 (E₆ : ℍ → ℂ) ^ 2 := by
    simp only [F12, coe_sub, coe_mcast, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hcoeΔ : ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) = ModularForm.discriminant := rfl
  have hfun : (F12 : ℍ → ℂ) = (1728 : ℂ) • ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ℍ → ℂ) := by
    rw [hcoeΔ]
    funext z
    simp only [F12, coe_sub, coe_mcast, coe_pow, Pi.sub_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    rw [discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← hq, hfun, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ)
    (CuspForm.discriminant : CuspForm 𝒮ℒ 12), hcoeΔ, PowerSeries.smul_eq_C_mul]

theorem intSeriesC_pow (K : Type) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_sub (K : Type) [Field K] (q r : PowerSeries ℤ) :
    intSeriesC K (q - r) = intSeriesC K q - intSeriesC K r := by
  simp [intSeriesC, map_sub]

theorem intSeriesC_X (K : Type) [Field K] : intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
  rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem jqModC_mul_delta (K : Type) [Field K] :
    jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein4 ^ 3) := by
  have hj : jqModC K = HahnSeries.single (-1 : ℤ) (1 : K) * intSeriesC K jNum := rfl
  calc jqModC K * intSeriesC K (PowerSeries.X * dedekindEtaUnit)
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K)) *
          (intSeriesC K jNum * intSeriesC K dedekindEtaUnit) := by
        rw [hj, intSeriesC_mul, intSeriesC_X]; ring
    _ = intSeriesC K (jNum * dedekindEtaUnit) := by
        rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, ← intSeriesC_mul]
        rw [show (HahnSeries.single (0 : ℤ) (1 : K)) = 1 from rfl, one_mul]
    _ = intSeriesC K (eisenstein4 ^ 3) := by
        rw [jNum, mul_assoc, mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one]

theorem jqModC_sub_mul_delta (K : Type) [Field K] :
    (jqModC K - 1728) * intSeriesC K (PowerSeries.X * dedekindEtaUnit) = intSeriesC K (eisenstein6 ^ 2) := by
  have h := congrArg (intSeriesC K) eisenstein4_cube_sub_eisenstein6_sq
  rw [intSeriesC_sub, intSeriesC_mul] at h
  rw [sub_mul, jqModC_mul_delta]
  have hC : intSeriesC K (PowerSeries.C (1728 : ℤ)) = 1728 := by
    rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast, Int.cast_ofNat, map_ofNat]
  rw [hC] at h
  linear_combination h

end DivTrivAux

open DivTrivAux

theorem solution
    (κ : Type) [Field κ] (M : ℕ) [NeZero M]
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (k : ℕ) (g : ModularForm (Gamma1 M) (k : ℤ)) (pg : PowerSeries ℤ) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC κ pg ≠ 0)
    (t : ↥(ModularCurve.x1FunctionFieldC κ M))
    (ht : (t : LaurentSeries κ) =
      intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) / intSeriesC κ (pg ^ 12))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (htx : x.ord t = 0) :
    (3 : ℤ) ∣ (k : ℤ) * x.ord J ∧
      (2 : ℤ) ∣ (k : ℤ) * x.ord (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) := by
  classical
  have hΓ : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := Subgroup.map_le_range _ _
  have hT : ModularGroup.T ∈ Gamma1 M := by
    rw [Gamma1_mem]; simp [ModularGroup.T]
  have h1per : (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, hT, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

  have hIpow : ∀ {w : ℤ} (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w)
      (pf : PowerSeries ℤ), IsIntegralQExp f pf → ∀ n : ℕ, IsIntegralQExp (f.pow n) (pf ^ n) := by
    intro w f pf hf n
    unfold IsIntegralQExp at hf ⊢
    rw [map_pow, hf, ModularForm.qExpansion_pow one_pos h1per]
  have hE4 : IsIntegralQExp (restrictForm hΓ E₄) eisenstein4 := isIntegralQExp_E4
  have hE6 : IsIntegralQExp (restrictForm hΓ E₆) eisenstein6 := isIntegralQExp_E6
  have hE4k := hIpow (restrictForm hΓ E₄) eisenstein4 hE4 k
  have hE6k := hIpow (restrictForm hΓ E₆) eisenstein6 hE6 k
  have hg4 := hIpow g pg hg 4
  have hg6 := hIpow g pg hg 6
  have hcast : ∀ {a b : ℤ} (hab : a = b) (f : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) a)
      (pf : PowerSeries ℤ), IsIntegralQExp f pf → IsIntegralQExp (ModularForm.mcast hab f) pf := by
    intro a b hab f pf hf
    unfold IsIntegralQExp at hf ⊢
    rw [coe_mcast]; exact hf

  have hg4ne : intSeriesC κ (pg ^ 4) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hg6ne : intSeriesC κ (pg ^ 6) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hg12ne : intSeriesC κ (pg ^ 12) ≠ 0 := by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0
  have hΔne : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
    rw [intSeriesC_mul]
    refine mul_ne_zero ?_ ?_
    · rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
      exact HahnSeries.single_ne_zero one_ne_zero
    · intro h0
      have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
      have h2 := congrArg (PowerSeries.coeff 0) h1
      rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit,
        map_one, map_zero] at h2
      exact one_ne_zero h2
  have hE4ne : intSeriesC κ eisenstein4 ≠ 0 := by
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eisenstein4,
      map_one, map_zero] at h2
    exact one_ne_zero h2
  have hE6ne : intSeriesC κ eisenstein6 ≠ 0 := by
    intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (PowerSeries.coeff 0) h1
    have h3 : PowerSeries.coeff 0 eisenstein6 = 1 := by simp [eisenstein6]
    rw [PowerSeries.coeff_map, h3, map_one, map_zero] at h2
    exact one_ne_zero h2

  have hmem : ∀ {w : ℤ} (F G : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w) (pF pG : PowerSeries ℤ),
      IsIntegralQExp F pF → IsIntegralQExp G pG → intSeriesC κ pG ≠ 0 →
      intSeriesC κ pF / intSeriesC κ pG ∈ ModularCurve.x1FunctionFieldC κ M := by
    intro w F G pF pG hF hG hG0
    rw [x1FunctionFieldC, qExpFunctionFieldC]
    exact IntermediateField.subset_adjoin _ _ ⟨w, F, G, pF, pG, hF, hG, hG0, rfl⟩
  have hwa : ((k : ℕ) : ℤ) * 4 = ((4 : ℕ) : ℤ) * (k : ℤ) := by push_cast; ring
  have hwc : ((k : ℕ) : ℤ) * 6 = ((6 : ℕ) : ℤ) * (k : ℤ) := by push_cast; ring
  have hamem := hmem (ModularForm.mcast hwa ((restrictForm hΓ E₄).pow k)) (g.pow 4) (eisenstein4 ^ k) (pg ^ 4)
    (hcast hwa _ _ hE4k) hg4 hg4ne
  have hcmem := hmem (ModularForm.mcast hwc ((restrictForm hΓ E₆).pow k)) (g.pow 6) (eisenstein6 ^ k) (pg ^ 6)
    (hcast hwc _ _ hE6k) hg6 hg6ne
  set a : ↥(ModularCurve.x1FunctionFieldC κ M) := ⟨_, hamem⟩ with ha
  set c : ↥(ModularCurve.x1FunctionFieldC κ M) := ⟨_, hcmem⟩ with hc

  set e4 := intSeriesC κ eisenstein4 with he4
  set e6 := intSeriesC κ eisenstein6 with he6
  set eg := intSeriesC κ pg with heg
  set eΔ := intSeriesC κ (PowerSeries.X * dedekindEtaUnit) with heΔ
  have hj4 : ModularCurve.jqModC κ = e4 ^ 3 / eΔ := by
    rw [eq_div_iff hΔne, he4, ← intSeriesC_pow]; exact jqModC_mul_delta κ
  have hj6 : ModularCurve.jqModC κ - 1728 = e6 ^ 2 / eΔ := by
    rw [eq_div_iff hΔne, he6, ← intSeriesC_pow]; exact jqModC_sub_mul_delta κ
  have hacoe : ((a : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = e4 ^ k / eg ^ 4 := by
    rw [ha]; show intSeriesC κ (eisenstein4 ^ k) / intSeriesC κ (pg ^ 4) = _; rw [intSeriesC_pow, intSeriesC_pow]
  have hccoe : ((c : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = e6 ^ k / eg ^ 6 := by
    rw [hc]; show intSeriesC κ (eisenstein6 ^ k) / intSeriesC κ (pg ^ 6) = _; rw [intSeriesC_pow, intSeriesC_pow]
  have htcoe : ((t : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = eΔ ^ k / eg ^ 12 := by
    rw [ht, intSeriesC_pow, intSeriesC_pow]
  have h1728 : ((algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = 1728 := by
    rw [map_ofNat]; push_cast; rfl

  have ha3 : a ^ 3 = J ^ k * t := by
    apply Subtype.ext
    push_cast
    rw [hacoe, hJ, htcoe, hj4, div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      mul_comm (eΔ ^ k) (eg ^ 12), mul_div_mul_right _ _ (pow_ne_zero _ hΔne)]
    ring
  have h1728' : algebraMap κ (LaurentSeries κ) 1728 = 1728 := map_ofNat _ _
  have hc2 : c ^ 2 = (J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728) ^ k * t := by
    apply Subtype.ext
    push_cast
    rw [hccoe, h1728', hJ, htcoe, hj6, div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm,
      mul_comm (eΔ ^ k) (eg ^ 12), mul_div_mul_right _ _ (pow_ne_zero _ hΔne)]
    ring

  have hne_of_coe : ∀ {z : ↥(ModularCurve.x1FunctionFieldC κ M)}, (z : LaurentSeries κ) ≠ 0 → z ≠ 0 := fun h h0 => h (by rw [h0]; rfl)
  have ha0 : a ≠ 0 := hne_of_coe (by rw [hacoe]; exact div_ne_zero (pow_ne_zero _ hE4ne) (pow_ne_zero _ hg0))
  have hc0 : c ≠ 0 := hne_of_coe (by rw [hccoe]; exact div_ne_zero (pow_ne_zero _ hE6ne) (pow_ne_zero _ hg0))
  have ht0 : t ≠ 0 := hne_of_coe (by rw [htcoe]; exact div_ne_zero (pow_ne_zero _ hΔne) (pow_ne_zero _ hg0))
  have hJ0 : J ≠ 0 := hne_of_coe (by rw [hJ, hj4]; exact div_ne_zero (pow_ne_zero _ hE4ne) hΔne)
  have hJ'coe : ((J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = e6 ^ 2 / eΔ := by
    rw [AddSubgroupClass.coe_sub, h1728, hJ, hj6]
  have hJ' : J - algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) 1728 ≠ 0 :=
    hne_of_coe (by rw [hJ'coe]; exact div_ne_zero (pow_ne_zero _ hE6ne) hΔne)

  have hordpow : ∀ (f : ↥(ModularCurve.x1FunctionFieldC κ M)) (n : ℕ), x.ord (f ^ n) = (n : ℤ) * x.ord f := by
    intro f n; rw [← zpow_natCast]; exact x.ord_zpow f n
  refine ⟨Dvd.intro (x.ord a) ?_, Dvd.intro (x.ord c) ?_⟩
  · have h := congrArg x.ord ha3
    rw [hordpow, x.ord_mul (pow_ne_zero _ hJ0) ht0, hordpow, htx, add_zero] at h
    exact_mod_cast h
  · have h := congrArg x.ord hc2
    rw [hordpow, x.ord_mul (pow_ne_zero _ hJ') ht0, hordpow, htx, add_zero] at h
    exact_mod_cast h

end S_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_three_dvd_mul_ord_and_two_dvd_mul_ord_sub_of_ord_eq_zero_x1FunctionFieldC (solution)
