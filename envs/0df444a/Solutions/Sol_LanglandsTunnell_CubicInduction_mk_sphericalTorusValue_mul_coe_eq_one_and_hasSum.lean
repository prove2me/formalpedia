-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/634a93c9-1e99-5557-bf6f-5a15370df53c

import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum

set_option autoImplicit false

open Polynomial

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "sphericalTorusValue"
namespace SphericalGF
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem rec3 (e₁ e₂ e₃ : ℂ) (n : ℕ) :
    sphericalTorusValue e₁ e₂ e₃ (n + 3) =
      e₁ * sphericalTorusValue e₁ e₂ e₃ (n + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (n + 1) +
        e₃ * sphericalTorusValue e₁ e₂ e₃ n := by
  rfl

theorem coe_eq (P : ℂ[X]) (hP3 : P.natDegree ≤ 3) :
    (P : PowerSeries ℂ) =
      PowerSeries.C (P.coeff 0) + PowerSeries.C (P.coeff 1) * PowerSeries.X +
        PowerSeries.C (P.coeff 2) * PowerSeries.X ^ 2 + PowerSeries.C (P.coeff 3) * PowerSeries.X ^ 3 := by
  conv_lhs => rw [Polynomial.as_sum_range' P 4 (by omega)]
  simp [Finset.sum_range_succ, Polynomial.coe_add, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_mul_C_mul_X_pow (φ : PowerSeries ℂ) (c : ℂ) (k d : ℕ) :
    PowerSeries.coeff d (φ * (PowerSeries.C c * PowerSeries.X ^ k)) =
      if k ≤ d then c * PowerSeries.coeff (d - k) φ else 0 := by
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C]
  split_ifs <;> ring

theorem mk_mul_eq_one (P : ℂ[X]) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3) :
    PowerSeries.mk (sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3)) * (P : PowerSeries ℂ) = 1 := by
  set h := sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) with hh
  rw [coe_eq P hP3, hP0]
  refine PowerSeries.ext fun d => ?_
  have hX1 : PowerSeries.C (P.coeff 1) * PowerSeries.X =
      PowerSeries.C (P.coeff 1) * (PowerSeries.X : PowerSeries ℂ) ^ 1 := by rw [pow_one]
  rw [hX1, mul_add, mul_add, mul_add, map_add, map_add, map_add, coeff_mul_C_mul_X_pow,
    coeff_mul_C_mul_X_pow, coeff_mul_C_mul_X_pow, map_one, mul_one, PowerSeries.coeff_mk,
    PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_mk]
  rcases d with _ | _ | _ | n
  · simp [hh, sphericalTorusValue]
  · simp [hh, sphericalTorusValue]
  · simp [hh, sphericalTorusValue]; ring
  · have h3 : n + 1 + 1 + 1 = n + 3 := by ring
    simp only [h3, show (1 : ℕ) ≤ n + 3 by omega, show (2 : ℕ) ≤ n + 3 by omega,
      show (3 : ℕ) ≤ n + 3 by omega, if_true, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega,
      show (n + 3 = 0) = False by simp, if_false]
    rw [hh, rec3]
    ring

theorem norm_le_pow (e₁ e₂ e₃ : ℂ) (n : ℕ) :
    ‖sphericalTorusValue e₁ e₂ e₃ n‖ ≤ (max 1 (‖e₁‖ + ‖e₂‖ + ‖e₃‖)) ^ n := by
  set M := max 1 (‖e₁‖ + ‖e₂‖ + ‖e₃‖) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have he₁ : ‖e₁‖ ≤ M := le_trans (by nlinarith [norm_nonneg e₂, norm_nonneg e₃]) (le_max_right _ _)
  have he₂ : ‖e₂‖ ≤ M := le_trans (by nlinarith [norm_nonneg e₁, norm_nonneg e₃]) (le_max_right _ _)
  have hsum : ‖e₁‖ + ‖e₂‖ + ‖e₃‖ ≤ M := le_max_right _ _

  have key : ∀ m : ℕ, ‖sphericalTorusValue e₁ e₂ e₃ m‖ ≤ M ^ m ∧
      ‖sphericalTorusValue e₁ e₂ e₃ (m + 1)‖ ≤ M ^ (m + 1) ∧
      ‖sphericalTorusValue e₁ e₂ e₃ (m + 2)‖ ≤ M ^ (m + 2) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [sphericalTorusValue]
      · simpa [sphericalTorusValue] using he₁
      · simp only [sphericalTorusValue, zero_add]
        calc ‖e₁ ^ 2 - e₂‖ ≤ ‖e₁ ^ 2‖ + ‖e₂‖ := norm_sub_le _ _
          _ = ‖e₁‖ * ‖e₁‖ + ‖e₂‖ := by rw [norm_pow, pow_two]
          _ ≤ ‖e₁‖ * M + ‖e₂‖ * M := by
              nlinarith [norm_nonneg e₁, norm_nonneg e₂]
          _ = (‖e₁‖ + ‖e₂‖) * M := by ring
          _ ≤ M * M := by nlinarith [norm_nonneg e₃]
          _ = M ^ (0 + 2) := by ring
    | succ m ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      refine ⟨h1, by simpa [add_assoc] using h2, ?_⟩
      have h3 : m + 1 + 2 = m + 3 := by ring
      rw [h3, rec3]
      calc ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (m + 2) - e₂ * sphericalTorusValue e₁ e₂ e₃ (m + 1) +
              e₃ * sphericalTorusValue e₁ e₂ e₃ m‖
          ≤ ‖e₁ * sphericalTorusValue e₁ e₂ e₃ (m + 2)‖ + ‖e₂ * sphericalTorusValue e₁ e₂ e₃ (m + 1)‖ +
              ‖e₃ * sphericalTorusValue e₁ e₂ e₃ m‖ := by
              refine (norm_add_le _ _).trans ?_
              exact add_le_add (norm_sub_le (e₁ * sphericalTorusValue e₁ e₂ e₃ (m + 2))
                (e₂ * sphericalTorusValue e₁ e₂ e₃ (m + 1))) le_rfl
        _ = ‖e₁‖ * ‖sphericalTorusValue e₁ e₂ e₃ (m + 2)‖ + ‖e₂‖ * ‖sphericalTorusValue e₁ e₂ e₃ (m + 1)‖ +
              ‖e₃‖ * ‖sphericalTorusValue e₁ e₂ e₃ m‖ := by rw [norm_mul, norm_mul, norm_mul]
        _ ≤ ‖e₁‖ * M ^ (m + 2) + ‖e₂‖ * M ^ (m + 2) + ‖e₃‖ * M ^ (m + 2) := by
              have hp1 : M ^ (m + 1) ≤ M ^ (m + 2) := pow_le_pow_right₀ hM1 (by omega)
              have hp0 : M ^ m ≤ M ^ (m + 2) := pow_le_pow_right₀ hM1 (by omega)
              gcongr
              · exact h1.trans hp1
              · exact h0.trans hp0
        _ = (‖e₁‖ + ‖e₂‖ + ‖e₃‖) * M ^ (m + 2) := by ring
        _ ≤ M * M ^ (m + 2) := by gcongr
        _ = M ^ (m + 3) := by ring
  exact (key n).1

end LanglandsTunnell.CubicInduction.SphericalGF

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "sphericalTorusValue"
namespace SphericalGF
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

theorem eval_ne_zero_and_hasSum (P : ℂ[X]) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3) (X₀ : ℂ)
    (hX : ‖X₀‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) < 1) :
    P.eval X₀ ≠ 0 ∧
      HasSum (fun n : ℕ => sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n * X₀ ^ n)
        (P.eval X₀)⁻¹ := by
  set h := sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) with hh
  set M := max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) with hM
  have hM' : max 1 (‖-P.coeff 1‖ + ‖P.coeff 2‖ + ‖-P.coeff 3‖) = M := by rw [norm_neg, norm_neg]
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hr0 : 0 ≤ ‖X₀‖ * M := mul_nonneg (norm_nonneg _) hM0

  have hbound : ∀ n, ‖h n * X₀ ^ n‖ ≤ (‖X₀‖ * M) ^ n := fun n => by
    rw [norm_mul, norm_pow, mul_pow, mul_comm]
    have := norm_le_pow (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n
    rw [hM'] at this
    exact mul_le_mul_of_nonneg_left this (pow_nonneg (norm_nonneg _) _)
  have hsumm_norm : Summable fun n => ‖h n * X₀ ^ n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (summable_geometric_of_lt_one hr0 hX)
  have hsumm : Summable fun n => h n * X₀ ^ n := hsumm_norm.of_norm

  set g : ℕ → ℂ := fun n => P.coeff n * X₀ ^ n with hg
  have hg0 : ∀ n ∉ Finset.range 4, g n = 0 := fun n hn => by
    have hn4 : 4 ≤ n := by simpa using hn
    simp only [hg, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n), zero_mul]
  have hg_norm : Summable fun n => ‖g n‖ :=
    summable_of_ne_finset_zero (s := Finset.range 4) fun n hn => by rw [hg0 n hn, norm_zero]
  have hg_sum : ∑' n, g n = P.eval X₀ := by
    rw [tsum_eq_sum hg0, Polynomial.eval_eq_sum_range' (by omega : P.natDegree < 4)]

  have hcoeff : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, h kl.1 * P.coeff kl.2 = if n = 0 then 1 else 0 := by
    intro n
    have := congrArg (PowerSeries.coeff n) (mk_mul_eq_one P hP0 hP3)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at this
    simpa only [PowerSeries.coeff_mk, Polynomial.coeff_coe, ← hh] using this
  have hprod : (∑' n, h n * X₀ ^ n) * P.eval X₀ = 1 := by
    rw [← hg_sum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsumm_norm hg_norm]
    have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, h kl.1 * X₀ ^ kl.1 * g kl.2 =
        (if n = 0 then 1 else 0) := by
      intro n
      have hfac : ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, h kl.1 * X₀ ^ kl.1 * g kl.2 =
          (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, h kl.1 * P.coeff kl.2) * X₀ ^ n := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun kl hkl => ?_
        have hn : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
        simp only [hg]
        rw [← hn, pow_add]
        ring
      rw [hfac, hcoeff n]
      split_ifs with h0
      · rw [h0, pow_zero, one_mul]
      · rw [zero_mul]
    simp_rw [hterm]
    exact (tsum_ite_eq 0 (fun _ => (1 : ℂ))).trans rfl
  have hne : P.eval X₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact zero_ne_one hprod
  refine ⟨hne, ?_⟩
  have hval : ∑' n, h n * X₀ ^ n = (P.eval X₀)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [← hval]
  exact hsumm.hasSum

end LanglandsTunnell.CubicInduction.SphericalGF

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum.LanglandsTunnell.CubicInduction in
theorem solution
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3) :
    PowerSeries.mk (sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3)) * (P : PowerSeries ℂ) = 1 ∧
    (∀ n : ℕ, ‖sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n‖ ≤
      (max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖)) ^ n) ∧
    ∀ x : ℂ, ‖x‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) < 1 →
      P.eval x ≠ 0 ∧
      HasSum (fun n : ℕ => sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n * x ^ n)
        (P.eval x)⁻¹ :=
  ⟨SphericalGF.mk_mul_eq_one P hP0 hP3,
    fun n => by simpa only [norm_neg] using SphericalGF.norm_le_pow (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n,
    fun x hx => SphericalGF.eval_ne_zero_and_hasSum P hP0 hP3 x hx⟩

end S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum (solution)
