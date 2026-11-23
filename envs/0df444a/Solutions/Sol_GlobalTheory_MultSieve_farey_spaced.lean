-- Prove2me | solution 1 for GlobalTheory.MultSieve.farey_spaced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.340843+00:00
-- url     : https://prove2.me/submissions/1012a09e-cf05-4b42-9fa5-f6e58b9d24f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.MultSieve
namespace GlobalTheory.MultSieve
theorem _root_.solution (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast hb)
  have hc1 : (c : ℝ) / r < 1 := (div_lt_one hr0).2 (by exact_mod_cast hc)
  have hb0 : 0 ≤ (b : ℝ) / q := by positivity
  have hc0 : 0 ≤ (c : ℝ) / r := by positivity
  have hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0 := by
    intro h
    have h1 : (k : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < k := by linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have : k = 0 := by omega
    subst this
    apply hne
    simp at h
    linarith
  have he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r) := by
    push_cast; field_simp
  rw [he] at hk ⊢
  have hm : (b * r - c * q - k * q * r : ℤ) ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  have hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
  rw [sq]
  gcongr
end GlobalTheory.MultSieve
