-- Prove2me | solution 1 for GlobalTheory.LLower.norm_LFunction_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:04.604017+00:00
-- url     : https://prove2.me/submissions/869cb165-e4a9-457c-bb95-dd33c450ff4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Theorems.Thm_GlobalTheory_LLower_norm_LSeries_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LLower
namespace GlobalTheory.LLower
theorem _root_.solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  have hre : 1 < s.re := hs
  have hσ : 0 < s.re := by linarith
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hb : ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ ≤ s.re / (s.re - 1) := by
    refine norm_LSeries_le (fun n => ?_) hre
    rw [norm_mul]
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have h2 : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    calc ‖χ n‖ * ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hn : ‖LSeries (fun n => (χ n : ℂ)) s‖ * ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ = 1 := by
    have hprod' : LSeries (fun n => (χ n : ℂ)) s * LSeries (fun n => χ n * (moebius n : ℂ)) s = 1 :=
      hprod
    rw [← norm_mul, hprod', norm_one]
  have hd : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ hσ]
  have hA : 0 ≤ ‖LSeries (fun n => (χ n : ℂ)) s‖ := norm_nonneg _
  calc s.re - 1 = (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ *
        ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖) := by rw [hn, mul_one]
    _ ≤ (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ * (s.re / (s.re - 1))) := by
        gcongr
    _ = ‖LSeries (fun n => (χ n : ℂ)) s‖ * s.re := by
        field_simp
end GlobalTheory.LLower
