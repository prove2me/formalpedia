-- Prove2me | solution 1 for OAI.FiniteCircle.primeInterval_card_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:15:21.939275+00:00
-- url     : https://prove2.me/submissions/94e1bb30-9d84-4347-bed9-12c23c594398

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Primes.lean:L101-L152
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.primeInterval_card_cubic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Theorems.Thm_OAI_FiniteCircle_centralBinom_le_interval

-- ---- from OAI.Combinatorics.FiniteCircle.Primes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem centralBinom_le_interval_card (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) * (2*n)^(primeInterval n).card := by
  refine (centralBinom_le_interval n hn).trans (Nat.mul_le_mul_left _ ?_)
  calc
    _ ≤ ∏ _p ∈ primeInterval n, 2*n := Finset.prod_le_prod' (fun p hp =>
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)
    _ = _ := by simp

theorem log_le_linear_million {x : ℝ} (hx : 1000000 ≤ x) :
    Real.log x ≤ x / 500 := by
  have hp : 0 < x := by linarith
  have hs : Real.sqrt x ≤ x/1000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := mul_nonneg (show 0 ≤ x-1000000 by linarith) hp.le
      nlinarith
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hl
  linarith

theorem primeInterval_card_cubic (h : ℕ) (hh : 1000000 ≤ h) :
    h^2 ≤ (primeInterval (h^3)).card := by
  have htwo : 2 ≤ h := by omega
  have hN : 4 ≤ h^3 := by nlinarith [Nat.pow_le_pow_left htwo 3]
  have hH : (1000000:ℝ) ≤ h := by exact_mod_cast hh
  have hp : (0:ℝ) < h := by positivity
  have hhlog := log_le_linear_million hH
  have hlog0 : 0 ≤ Real.log (h:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
  have hlog4 : (3:ℝ)/4 ≤ Real.log 4 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(4:ℝ)⁻¹)
    rw [Real.log_inv] at hl
    norm_num at hl ⊢
    linarith
  have hsqrt : Nat.sqrt (2*h^3) ≤ 2*h^2 := by
    have he : 2*h^3 ≤ (2*h^2)^2 := by nlinarith [sq_nonneg (h:ℤ), Nat.pow_le_pow_left htwo 2]
    exact (Nat.sqrt_le_sqrt he).trans_eq (Nat.sqrt_eq' _)
  by_contra hn
  have hc : (primeInterval (h^3)).card ≤ h^2 := by omega
  have hbin := centralBinom_le_interval_card (h^3) (by omega)
  have hpow : 4^(h^3) < h^3 * ((2*h^3)^(3*h^2) * 4^(2*h^3/3)) := by
    apply (Nat.four_pow_lt_mul_centralBinom (h^3) hN).trans_le
    apply Nat.mul_le_mul_left
    apply hbin.trans
    calc
      _ = (2*h^3)^(Nat.sqrt (2*h^3)+(primeInterval (h^3)).card)*4^(2*h^3/3) := by
        rw [pow_add]
        ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hpowR : (4:ℝ)^(h^3) < (h:ℝ)^3 *((2*(h:ℝ)^3)^(3*h^2)*4^(2*h^3/3)) := by
    exact_mod_cast hpow
  have hlog := (Real.log_lt_log (by positivity) hpowR)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  have hlog2 : Real.log (2*(h:ℝ)^3) ≤ 4*Real.log (h:ℝ) := by
    have ht : 2*(h:ℝ)^3 ≤ (h:ℝ)^4 := by
      have hh2 : (2:ℝ) ≤ h := by exact_mod_cast htwo
      nlinarith [mul_nonneg (show 0 ≤ (h:ℝ)-2 by linarith) (show 0 ≤ (h:ℝ)^3 by positivity)]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by positivity) ht
  have hdiv : ((2*h^3/3:ℕ):ℝ) ≤ 2*(h:ℝ)^3/3 := by
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2*h^3) (n := 3))
  have hmul := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ Real.log 4 by linarith)
  have hmul2 := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ (3*h^2:ℕ) by positivity)
  have hbound : (h:ℝ)^3*Real.log 4/3 < (3+12*(h:ℝ)^2)*Real.log h := by
    push_cast at hlog hmul2
    nlinarith
  have hlarge : (3+12*(h:ℝ)^2)*Real.log h ≤ 13*(h:ℝ)^2*((h:ℝ)/500) := by
    have hh2 : (2:ℝ) ≤ h := by exact_mod_cast htwo
    have ha : 3+12*(h:ℝ)^2 ≤ 13*(h:ℝ)^2 := by nlinarith
    exact mul_le_mul ha hhlog hlog0 (by positivity)
  have hlower := mul_le_mul_of_nonneg_left hlog4 (show 0 ≤ (h:ℝ)^3/3 by positivity)
  have hcube : 0 < (h:ℝ)^3 := by positivity
  nlinarith

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

end StandingPrimes

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.primeInterval_card_cubic := @_root_.OAI.FiniteCircle.primeInterval_card_cubic
