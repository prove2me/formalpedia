-- Prove2me | solution 1 for ModularCurve.exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cc19280e-a73a-5a99-b2a2-99817472c484

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne

set_option autoImplicit false
set_option maxHeartbeats 8000000

open ModularCurve
open scoped MatrixGroups ModularForm

namespace FIdxLevelOne

open ModularForm UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

noncomputable abbrev q4 : PowerSeries ℂ := qExpansion 1 (E₄ : ℍ → ℂ)
noncomputable abbrev qΔ : PowerSeries ℂ := qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)

noncomputable def monomialSpan (m : ℕ) : Submodule ℂ (PowerSeries ℂ) :=
  Submodule.span ℂ (Set.range fun b : Fin (m + 1) => q4 ^ (3 * (m - b)) * qΔ ^ (b : ℕ))

theorem monomial_mem (m : ℕ) (b : ℕ) (hb : b ≤ m) :
    q4 ^ (3 * (m - b)) * qΔ ^ b ∈ monomialSpan m :=
  Submodule.subset_span ⟨⟨b, Nat.lt_succ_of_le hb⟩, rfl⟩

theorem q4_coeff_zero : PowerSeries.coeff 0 q4 = 1 :=
  E_qExpansion_coeff_zero (by norm_num) (by decide)

theorem qExpansion_mem_monomialSpan (m : ℕ) :
    ∀ (k : ℤ) (hk : k = 12 * (m : ℤ)) (h : ModularForm 𝒮ℒ k), qExpansion 1 (h : ℍ → ℂ) ∈ monomialSpan m := by
  induction m with
  | zero =>
    intro k hk h
    simp only [Nat.cast_zero, mul_zero] at hk
    subst hk
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const h
    have hh : h = c • (1 : ModularForm 𝒮ℒ 0) := by
      ext z
      rw [hc, IsGLPos.smul_apply]
      simp
    rw [hh, IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_one]
    refine Submodule.smul_mem _ _ ?_
    have := monomial_mem 0 0 le_rfl
    simpa using this
  | succ m ih =>
    intro k hk h
    set a₀ : ℂ := PowerSeries.coeff 0 (qExpansion 1 (h : ℍ → ℂ)) with ha₀
    let P : ModularForm 𝒮ℒ k := (E₄.pow (3 * (m + 1))).mcast (by rw [hk]; push_cast; ring)
    have hP : qExpansion 1 (P : ℍ → ℂ) = q4 ^ (3 * (m + 1)) := by
      simp only [P, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    let g : ModularForm 𝒮ℒ k := h - a₀ • P
    have hg : qExpansion 1 (g : ℍ → ℂ) = qExpansion 1 (h : ℍ → ℂ) - a₀ • q4 ^ (3 * (m + 1)) := by
      simp only [g]
      rw [coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, IsGLPos.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hP]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (g : ℍ → ℂ)) = 0 := by
      have h4 : PowerSeries.coeff 0 (q4 ^ (3 * (m + 1))) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, q4_coeff_zero, one_pow]
      rw [hg, map_sub, map_smul, h4, smul_eq_mul, mul_one, ha₀, sub_self]

    have hΔ := ModularForm.qExpansion_eq_qExpansion_discriminant_mul g hg0
    have hk' : k - 12 = 12 * (m : ℤ) := by rw [hk]; push_cast; ring
    have hIH := ih (k - 12) hk' (CuspForm.discriminantEquiv (g.toCuspForm hg0))

    have hh : qExpansion 1 (h : ℍ → ℂ) =
        a₀ • q4 ^ (3 * (m + 1)) +
          qΔ * qExpansion 1 (CuspForm.discriminantEquiv (g.toCuspForm hg0) : ℍ → ℂ) := by
      rw [← hΔ, hg]; abel
    rw [hh]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · have := monomial_mem (m + 1) 0 (Nat.zero_le _)
      simpa using this
    ·
      refine Submodule.span_induction (p := fun x _ => qΔ * x ∈ monomialSpan (m + 1))
        ?_ ?_ ?_ ?_ hIH
      · rintro _ ⟨b, rfl⟩
        have hb : (b : ℕ) ≤ m := Nat.lt_succ_iff.mp b.2
        have := monomial_mem (m + 1) (b + 1) (Nat.succ_le_succ hb)
        rw [show 3 * (m + 1 - ((b : ℕ) + 1)) = 3 * (m - b) by omega, pow_succ] at this
        rw [show qΔ * (q4 ^ (3 * (m - ↑b)) * qΔ ^ (b : ℕ)) =
          q4 ^ (3 * (m - ↑b)) * (qΔ ^ (b : ℕ) * qΔ) by ring]
        exact this
      · simp
      · intro x y _ _ hx hy
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ _ hx

end FIdxLevelOne

namespace Level1PolyAux

open ModularForm UpperHalfPlane EisensteinSeries

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

theorem intSeriesC_pow (K : Type) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

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

theorem ofPowerSeries_q4 :
    HahnSeries.ofPowerSeries ℤ ℂ FIdxLevelOne.q4 = intSeriesC ℂ eisenstein4 := by
  rw [intSeriesC]
  exact congrArg (HahnSeries.ofPowerSeries ℤ ℂ) isIntegralQExp_E4.symm

theorem ofPowerSeries_qΔ :
    HahnSeries.ofPowerSeries ℤ ℂ FIdxLevelOne.qΔ = intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit) := by
  rw [intSeriesC, FIdxLevelOne.qΔ, ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]

theorem monomial_eq (m b : ℕ) (hb : b ≤ m) :
    HahnSeries.ofPowerSeries ℤ ℂ (FIdxLevelOne.q4 ^ (3 * (m - b)) * FIdxLevelOne.qΔ ^ b) =
      jqModC ℂ ^ (m - b) * intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit) ^ m := by
  rw [map_mul, map_pow, map_pow, ofPowerSeries_q4, ofPowerSeries_qΔ, pow_mul,
    ← intSeriesC_pow ℂ eisenstein4 3, ← jqModC_mul_delta ℂ, mul_pow, mul_assoc, ← pow_add,
    Nat.sub_add_cancel hb]

end Level1PolyAux

open Level1PolyAux

theorem solution
    (m : ℕ) {k : ℤ} (hk : k = 12 * (m : ℤ))
    (h : ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range k) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑h : UpperHalfPlane → ℂ)) =
        Polynomial.aeval (ModularCurve.jqModC ℂ) P *
          ModularCurve.intSeriesC ℂ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ m) := by
  classical
  have hmem := FIdxLevelOne.qExpansion_mem_monomialSpan m k hk h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  refine ⟨∑ b : Fin (m + 1), Polynomial.C (c b) * Polynomial.X ^ (m - (b : ℕ)), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun b _ => ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le (c b) _).trans (Nat.sub_le _ _)
  · have hC : ∀ a : ℂ, algebraMap ℂ (LaurentSeries ℂ) a = HahnSeries.C a := by
      intro a
      rw [HahnSeries.algebraMap_apply', show algebraMap ℂ (PowerSeries ℂ) a = PowerSeries.C a from rfl,
        HahnSeries.ofPowerSeries_C]
    rw [← hc, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hb : (b : ℕ) ≤ m := Nat.lt_succ_iff.mp b.2
    rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, monomial_eq m b hb, map_mul,
      Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hC, mul_assoc, intSeriesC_pow]

end S_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
end P2MW
export P2MW.S_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne (solution)
