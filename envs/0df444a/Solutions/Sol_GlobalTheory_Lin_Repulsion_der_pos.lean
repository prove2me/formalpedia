-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.der_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:44.977025+00:00
-- url     : https://prove2.me/submissions/dae209b0-b98f-4355-91aa-cbea99c53d8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_Lin_Repulsion_summable_der

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h : χ₁ ^ 2 = 1) (k : ℕ) (t : ℝ) :
    0 ≤ (derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) k (2 + (0 : ℝ) * I) +
      derSeries (fun n : ℕ => χ₁ (n : ZMod q)) k (2 + (0 : ℝ) * I) +
      derSeries (fun n : ℕ => χ (n : ZMod q)) k (2 + t * I) +
      derSeries (fun n : ℕ => (χ * χ₁) (n : ZMod q)) k (2 + t * I)).re := by
  have s1 := summable_der _ (fun n : ℕ => (1 : DirichletCharacter ℂ q).norm_le_one (n : ZMod q)) k 0
  have s2 := summable_der _ (fun n : ℕ => χ₁.norm_le_one (n : ZMod q)) k 0
  have s3 := summable_der _ (fun n : ℕ => χ.norm_le_one (n : ZMod q)) k t
  have s4 := summable_der _ (fun n : ℕ => (χ * χ₁).norm_le_one (n : ZMod q)) k t
  unfold derSeries
  rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← ((s1.add s2).add s3).tsum_add s4,
    Complex.re_tsum (((s1.add s2).add s3).add s4)]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hu : IsUnit (n : ZMod q)
  swap
  · simp [MulChar.map_nonunit _ hu]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : (n : ℂ) ^ (-((2 : ℂ) + t * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hn']
    congr 1; push_cast; ring
  have e0 : (n : ℂ) ^ (-((2 : ℂ) + (0 : ℝ) * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    congr 1; push_cast; ring
  set u : ℂ := χ n * (n : ℂ) ^ (-(t * I) : ℂ) with hudef
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hudef, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    simpa using χ.norm_le_one (n : ZMod q)
  have hre : 0 ≤ 1 + u.re := by have := (Complex.abs_re_le_norm u).trans hu1; linarith [(abs_le.1 this).1]
  have hsq : χ₁ n ^ 2 = 1 := by
    rw [← MulChar.pow_apply' _ two_ne_zero, h, MulChar.one_apply hu]
  set A : ℝ := Λ n * (Real.log n ^ k / k.factorial) * (n : ℝ) ^ (-2 : ℝ) with hA
  have hA0 : 0 ≤ A := by
    have := Real.log_natCast_nonneg n
    have := vonMangoldt_nonneg (n := n)
    positivity
  rw [e1, e0, MulChar.one_apply hu, MulChar.mul_apply]
  have key : ∀ ε : ℝ, χ₁ n = ε → 0 ≤ 1 + ε → 0 ≤ (((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) +
      ((Λ n : ℝ) : ℂ) * (χ n * χ₁ n) * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ))).re := by
    intro ε hε h0
    have : ((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) +
      ((Λ n : ℝ) : ℂ) * (χ n * χ₁ n) * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) = ((A * (1 + ε) : ℝ) : ℂ) * (1 + u) := by
      rw [hε, hA, hudef]; simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one]; ring
    rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
    positivity
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq.trans (one_pow 2).symm) with h1 | h1
  · exact key 1 (by simpa using h1) (by norm_num)
  · exact key (-1) (by simpa using h1) (by norm_num)
end GlobalTheory.Lin.Repulsion
