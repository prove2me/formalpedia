-- Prove2me | solution 1 for OAI.FiniteCircle.mask_descent_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:09:14.080204+00:00
-- url     : https://prove2.me/submissions/fc82f7f3-eaba-4835-b374-d6210b0b76f4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedDescent.lean:L264-L287
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_descent_numeric. The node keeps its source
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

 theorem resetBudget_bound {h T : ℕ} (hh : 1000000 ≤ h) (hT : 1 ≤ T) :
    resetBudget (h/100) T 1 h ≤ 200*T := by
  let K := h/100
  have hKh : h ≤ 198*(K-1) := by dsimp [K]; omega
  have hK : K ≤ 2*(K-1) := by dsimp [K]; omega
  have hmul := Nat.mul_le_mul_right T hKh
  have hmulK := Nat.mul_le_mul_left (2*(K-1)) hT
  unfold resetBudget
  apply Nat.div_le_of_le_mul
  change 1+h*T+K-2 ≤ (K-1)*(200*T)
  calc
    _ ≤ h*T+K := by omega
    _ ≤ 198*(K-1)*T+2*(K-1)*T := Nat.add_le_add hmul (hK.trans (by simpa using hmulK))
    _ = _ := by ring

 theorem mask_budget_exponent {n : ℕ} (hn : 1000000 ≤ n) :
    2*resetBudget (n^4/100) (n^2) 1 (n^4)+16*(n^4/100) ≤ n^4/2 := by
  have hn2 : 2000 ≤ n^2 := by nlinarith
  have hn4 : 1000000 ≤ n^4 := by nlinarith [sq_nonneg (n^2:ℤ)]
  have hb := resetBudget_bound hn4 (show 1 ≤ n^2 by omega)
  have hk := Nat.mul_div_le (n^4) 100
  have hp : 40000*n^2 ≤ 34*n^4 := by nlinarith
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

 theorem mask_descent_numeric {n : ℕ} (hn : 1000000 ≤ n) (he : n^4=2*(n^4/2)) :
    1/(n:ℝ)^(3*n^4) ≤ (1/((2:ℝ)^(n^4)*4)) * descentBound (n^4) (n^4/100) (n^2) 1 (n^4) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hh : 2 ≤ n^4 := by nlinarith [Nat.pow_le_pow_left (show 2≤n by omega) 4]
  have hf := four_eight_pow_le (show 256≤n by omega) hh he
  have hb := mask_budget_exponent hn
  let b := resetBudget (n^4/100) (n^2) 1 (n^4)
  let K := n^4/100
  have hex : n^4/2+(2*(n^4+b)+16*K) ≤ 3*n^4 := by dsimp [b,K]; omega
  have hg : (2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(2*(n^4+b))*(n:ℝ)^(16*K)) ≤ (n:ℝ)^(3*n^4) := by
    calc
      _ = (4*(8:ℝ)^(n^4)) * (n:ℝ)^(2*(n^4+b)+16*K) := by rw [show (8:ℝ)=2*4 by norm_num, mul_pow]; simp only [pow_add]; ring
      _ ≤ (n:ℝ)^(n^4/2) * (n:ℝ)^(2*(n^4+b)+16*K) := mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (n:ℝ)^(n^4/2+(2*(n^4+b)+16*K)) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hn1 hex
  unfold descentBound
  rw [one_div_mul_one_div]
  push_cast
  simp only [← pow_mul]
  change 1/(n:ℝ)^(3*n^4) ≤ 1/((2:ℝ)^(n^4)*4*((4:ℝ)^(n^4)*(n:ℝ)^(2*(n^4+b))*(n:ℝ)^(4*(4*K))))
  have heK : 4*(4*K)=16*K := by omega
  rw [heK]
  exact one_div_le_one_div_of_le (by positivity) hg

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_descent_numeric := @_root_.OAI.FiniteCircle.mask_descent_numeric
