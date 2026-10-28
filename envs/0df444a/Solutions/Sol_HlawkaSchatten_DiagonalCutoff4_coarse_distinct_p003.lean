-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:55:36.723828+00:00
-- url     : https://prove2.me/submissions/b4c899c5-1a89-4117-89d2-1f763b56a8f4

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p002_b018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_b037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_positive63
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p003_positive87
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_chart_positive_of_cases
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio_of_cases
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p003 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) :
    (∀ X orders signs, OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  have hex : ∀ c : Fin 88, c ≠ 63 → c ≠ 87 → ∀ X, OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c) → False := by
    intro c hn63 hn87 X hX
    by_cases hb0 : c.val < 3
    · exact coarse_distinct_p003_b000 p hpa hpb c (by omega) hb0 hn63 hn87 X hX
    by_cases hb1 : c.val < 5
    · exact coarse_distinct_p003_b001 p hpa hpb c (by omega) hb1 hn63 hn87 X hX
    by_cases hb2 : c.val < 7
    · exact coarse_distinct_p003_b002 p hpa hpb c (by omega) hb2 hn63 hn87 X hX
    by_cases hb3 : c.val < 9
    · exact coarse_distinct_p003_b003 p hpa hpb c (by omega) hb3 hn63 hn87 X hX
    by_cases hb4 : c.val < 11
    · exact coarse_distinct_p003_b004 p hpa hpb c (by omega) hb4 hn63 hn87 X hX
    by_cases hb5 : c.val < 12
    · exact coarse_distinct_p003_b005 p hpa hpb c (by omega) hb5 hn63 hn87 X hX
    by_cases hb6 : c.val < 16
    · exact coarse_distinct_p003_b006 p hpa hpb c (by omega) hb6 hn63 hn87 X hX
    by_cases hb7 : c.val < 17
    · exact coarse_distinct_p003_b007 p hpa hpb c (by omega) hb7 hn63 hn87 X hX
    by_cases hb8 : c.val < 19
    · exact coarse_distinct_p003_b008 p hpa hpb c (by omega) hb8 hn63 hn87 X hX
    by_cases hb9 : c.val < 20
    · exact coarse_distinct_p003_b009 p hpa hpb c (by omega) hb9 hn63 hn87 X hX
    by_cases hb10 : c.val < 22
    · exact coarse_distinct_p003_b010 p hpa hpb c (by omega) hb10 hn63 hn87 X hX
    by_cases hb11 : c.val < 25
    · exact coarse_distinct_p003_b011 p hpa hpb c (by omega) hb11 hn63 hn87 X hX
    by_cases hb12 : c.val < 26
    · exact coarse_distinct_p003_b012 p hpa hpb c (by omega) hb12 hn63 hn87 X hX
    by_cases hb13 : c.val < 28
    · exact coarse_distinct_p003_b013 p hpa hpb c (by omega) hb13 hn63 hn87 X hX
    by_cases hb14 : c.val < 30
    · exact coarse_distinct_p003_b014 p hpa hpb c (by omega) hb14 hn63 hn87 X hX
    by_cases hb15 : c.val < 32
    · exact coarse_distinct_p003_b015 p hpa hpb c (by omega) hb15 hn63 hn87 X hX
    by_cases hb16 : c.val < 33
    · exact coarse_distinct_p003_b016 p hpa hpb c (by omega) hb16 hn63 hn87 X hX
    by_cases hb17 : c.val < 34
    · exact coarse_distinct_p003_b017 p hpa hpb c (by omega) hb17 hn63 hn87 X hX
    by_cases hb18 : c.val < 37
    · exact wide_coarse_distinct_p002_b018 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb19 : c.val < 38
    · exact wide_coarse_distinct_p002_b018 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb20 : c.val < 41
    · exact coarse_distinct_p003_b020 p hpa hpb c (by omega) hb20 hn63 hn87 X hX
    by_cases hb21 : c.val < 43
    · exact coarse_distinct_p003_b021 p hpa hpb c (by omega) hb21 hn63 hn87 X hX
    by_cases hb22 : c.val < 44
    · exact coarse_distinct_p003_b022 p hpa hpb c (by omega) hb22 hn63 hn87 X hX
    by_cases hb23 : c.val < 46
    · exact coarse_distinct_p003_b023 p hpa hpb c (by omega) hb23 hn63 hn87 X hX
    by_cases hb24 : c.val < 54
    · exact coarse_distinct_p003_b024 p hpa hpb c (by omega) hb24 hn63 hn87 X hX
    by_cases hb25 : c.val < 62
    · exact coarse_distinct_p003_b025 p hpa hpb c (by omega) hb25 hn63 hn87 X hX
    by_cases hb26 : c.val < 66
    · exact coarse_distinct_p003_b026 p hpa hpb c (by omega) hb26 hn63 hn87 X hX
    by_cases hb27 : c.val < 68
    · exact coarse_distinct_p003_b027 p hpa hpb c (by omega) hb27 hn63 hn87 X hX
    by_cases hb28 : c.val < 69
    · exact coarse_distinct_p003_b028 p hpa hpb c (by omega) hb28 hn63 hn87 X hX
    by_cases hb29 : c.val < 70
    · exact coarse_distinct_p003_b029 p hpa hpb c (by omega) hb29 hn63 hn87 X hX
    by_cases hb30 : c.val < 71
    · exact coarse_distinct_p003_b030 p hpa hpb c (by omega) hb30 hn63 hn87 X hX
    by_cases hb31 : c.val < 73
    · exact coarse_distinct_p003_b031 p hpa hpb c (by omega) hb31 hn63 hn87 X hX
    by_cases hb32 : c.val < 77
    · exact coarse_distinct_p003_b032 p hpa hpb c (by omega) hb32 hn63 hn87 X hX
    by_cases hb33 : c.val < 78
    · exact coarse_distinct_p003_b033 p hpa hpb c (by omega) hb33 hn63 hn87 X hX
    by_cases hb34 : c.val < 79
    · exact coarse_distinct_p003_b034 p hpa hpb c (by omega) hb34 hn63 hn87 X hX
    by_cases hb35 : c.val < 81
    · exact coarse_distinct_p003_b035 p hpa hpb c (by omega) hb35 hn63 hn87 X hX
    by_cases hb36 : c.val < 85
    · exact coarse_distinct_p003_b036 p hpa hpb c (by omega) hb36 hn63 hn87 X hX
    exact coarse_distinct_p003_b037 p hpa hpb c (by omega) (by omega) hn63 hn87 X hX
  have hp : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X,
      OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (fun _ _ => true) →
      ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
    intro c hc
    rcases hc with rfl|rfl
    · exact coarse_distinct_p003_positive63 p hpa hpb
    · exact coarse_distinct_p003_positive87 p hpa hpb
  exact ⟨distinct_chart_positive_of_cases p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) hex,
    positive_chart_ratio_of_cases p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) hp⟩

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) :
    (∀ X orders signs, OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003 p hpa hpb

#print axioms solution
