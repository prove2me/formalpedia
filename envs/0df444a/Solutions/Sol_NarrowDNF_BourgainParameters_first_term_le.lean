-- Prove2me | solution 1 for NarrowDNF.BourgainParameters.first_term_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:10:53.236798+00:00
-- url     : https://prove2.me/submissions/1a207997-1d48-4970-bf8a-8b23eb25765b

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_BourgainParameters

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters

section


/-! Explicit numerical choices for the reconstructed Bourgain small-component
estimate. The Fourier threshold eta retains the paper's constants. -/

noncomputable section
namespace NarrowDNF.BourgainParameters








private theorem realCutoff_ge_one (k : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    1 ≤ realCutoff k e := by
  unfold realCutoff
  apply (le_div_iff₀ (pow_pos he0 10)).mpr
  simp only [one_mul]
  exact (pow_le_one₀ he0.le he1).trans (one_le_pow₀ (by norm_num))

private theorem cutoff_upper (k : ℕ) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) :
    (cutoff k e : ℝ) ≤ 2 * realCutoff k e := by
  have hR := realCutoff_ge_one k he0 he1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ realCutoff k e by linarith)
  change (⌈realCutoff k e⌉₊ : ℝ) ≤ _
  linarith

















end NarrowDNF.BourgainParameters

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.BourgainParameters
/-- The first term remains small after rounding M up to an integer. -/
theorem solution {k : ℕ} (hk : 1 ≤ k) {e : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) :
    (cutoff k e : ℝ)^k * (eta k e)^2 ≤ e^2 / (3:ℝ)^k := by
  have hM := pow_le_pow_left₀ (Nat.cast_nonneg (cutoff k e)) (cutoff_upper k he0 he1) k
  have hA : e^(10*k) ≤ e^2 := pow_le_pow_of_le_one he0.le he1 (by omega)
  have hpow : (2:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k ≤ (3:ℝ)^(20*k*k) := by
    calc
      _ ≤ (3:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k := by
        gcongr
        norm_num
      _ = (3:ℝ)^(k+18*k*k+k) := by simp only [pow_add]
      _ ≤ (3:ℝ)^(20*k*k) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hMp : (2*realCutoff k e)^k =
      (2:ℝ)^k * (3:ℝ)^(18*k*k) / e^(10*k) := by
    unfold realCutoff
    simp only [mul_pow, div_pow, ← pow_mul]
    ring
  have heta : (eta k e)^2 = (e^(10*k))^2 / (3:ℝ)^(20*k*k) := by
    unfold eta
    rw [div_pow, ← pow_mul (3:ℝ) (10*k^2) 2]
    congr 1
    congr 1
    ring
  calc
    _ ≤ (2*realCutoff k e)^k * (eta k e)^2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    _ = (2:ℝ)^k * (3:ℝ)^(18*k*k) * e^(10*k) / (3:ℝ)^(20*k*k) := by
      rw [hMp, heta]
      field_simp
    _ ≤ e^2 / (3:ℝ)^k := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      calc
        _ = e^(10*k) * ((2:ℝ)^k * (3:ℝ)^(18*k*k) * (3:ℝ)^k) := by ring
        _ ≤ e^2 * (3:ℝ)^(20*k*k) :=
          mul_le_mul hA hpow (by positivity) (sq_nonneg e)
