-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_descent_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:11:10.123047+00:00
-- url     : https://prove2.me/submissions/02d9c111-8a92-47b0-9b95-4ec4be050004

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean:L289-L312
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_descent_numeric. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.ExcludedDescent ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem pairResetBudget_bound {h T : ℕ} (hh : 1000000 ≤ h) (hT : 1 ≤ T) :
    pairResetBudget (h/100) T 1 h ≤ 200*T := by
  let K := h/100
  have hKh : h ≤ 198*(K-2) := by dsimp [K]; omega
  have hK : K ≤ 2*(K-2) := by dsimp [K]; omega
  have hmul := Nat.mul_le_mul_right T hKh
  have hmulK := Nat.mul_le_mul_left (2*(K-2)) hT
  unfold pairResetBudget
  apply Nat.div_le_of_le_mul
  change 1+h*T+K-3 ≤ (K-2)*(200*T)
  calc
    _ ≤ h*T+K := by omega
    _ ≤ 198*(K-2)*T+2*(K-2)*T := Nat.add_le_add hmul (hK.trans (by simpa using hmulK))
    _ = _ := by ring

 theorem excluded_budget_exponent {n : ℕ} (hn : 1000000 ≤ n) :
    3*pairResetBudget (n^4/100) (n^3) 1 (n^4)+20*(n^4/100) ≤ n^4 := by
  have hn3 : 1 ≤ n^3 := Nat.one_le_pow _ _ (by omega)
  have hn4 : 1000000 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2 ≤ n by omega) 4]
  have hb := pairResetBudget_bound hn4 hn3
  have hk := Nat.mul_div_le (n^4) 100
  have hp := Nat.mul_le_mul_right (n^3) (show 1000 ≤ n by omega)
  have he : n*n^3=n^4 := by ring
  rw [he] at hp
  omega

 theorem four_eight_pow_le {n h : ℕ} (hn : 256 ≤ n) (hh : 2 ≤ h) (he : h=2*(h/2)) :
    4*(8:ℝ)^h ≤ (n:ℝ)^(h/2) := by
  have hfour : (4:ℝ) ≤ 2^h := by
    calc
      (4:ℝ) = 2^2 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hh
  calc
    4*(8:ℝ)^h ≤ (2:ℝ)^h*8^h := mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = (16:ℝ)^h := by rw [← mul_pow]; norm_num
    _ = (256:ℝ)^(h/2) := by conv_lhs => rw [he, pow_mul]; norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hn) _

 theorem excluded_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * pairDescentBound (n^4) (n^4/100) (n^3) n 1 (n^4) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hh : 2 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 4]
  have hf := four_eight_pow_le (show 256≤n by omega) hh he
  have hb := excluded_budget_exponent hn
  let b := pairResetBudget (n^4/100) (n^3) 1 (n^4)
  let K := n^4/100
  have hex : n^4/2+(n^4+3*b+20*K) ≤ 3*n^4 := by dsimp [b,K]; omega
  have hg : (2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(n^4+3*b)*(n:ℝ)^(20*K)) ≤ (n:ℝ)^(3*n^4) := by
    calc
      _ = (4*(8:ℝ)^(n^4)) * (n:ℝ)^(n^4+3*b+20*K) := by rw [show (8:ℝ)=2*4 by norm_num, mul_pow]; simp only [pow_add]; ring
      _ ≤ (n:ℝ)^(n^4/2) * (n:ℝ)^(n^4+3*b+20*K) := mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (n:ℝ)^(n^4/2+(n^4+3*b+20*K)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hn1 hex
  unfold pairDescentBound
  rw [one_div_mul_one_div]
  push_cast
  simp only [← pow_mul]
  change 1/(n:ℝ)^(3*n^4) ≤ 1/((2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(n^4+3*b)*(n:ℝ)^(4*(5*K))))
  have heK : 4*(5*K)=20*K := by omega
  rw [heK]
  exact one_div_le_one_div_of_le (by positivity) hg

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_descent_numeric := @_root_.OAI.FiniteCircle.excluded_descent_numeric
