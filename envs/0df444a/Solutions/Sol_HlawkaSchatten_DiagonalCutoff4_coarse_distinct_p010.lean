-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:47.302446+00:00
-- url     : https://prove2.me/submissions/9ca5d6f1-c3bd-4547-8d6e-2d204dc8830b

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p009_b005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p009_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p009_b008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_b037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_positive63
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p010_positive87
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_chart_positive_of_cases
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio_of_cases
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p010 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) :
    (∀ X orders signs, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  have hex : ∀ c : Fin 88, c ≠ 63 → c ≠ 87 → ∀ X, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c) → False := by
    intro c hn63 hn87 X hX
    by_cases hb0 : c.val < 3
    · exact wide_coarse_distinct_p010_b000 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb1 : c.val < 5
    · exact wide_coarse_distinct_p010_b001 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb2 : c.val < 7
    · exact wide_coarse_distinct_p010_b002 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb3 : c.val < 9
    · exact wide_coarse_distinct_p010_b003 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb4 : c.val < 11
    · exact wide_coarse_distinct_p010_b004 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb5 : c.val < 13
    · exact wide_coarse_distinct_p009_b005 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb6 : c.val < 15
    · exact wide_coarse_distinct_p010_b006 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb7 : c.val < 17
    · exact wide_coarse_distinct_p009_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb8 : c.val < 19
    · exact wide_coarse_distinct_p009_b008 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb9 : c.val < 20
    · exact wide_coarse_distinct_p010_b009 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb10 : c.val < 21
    · exact wide_coarse_distinct_p010_b010 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb11 : c.val < 22
    · exact wide_coarse_distinct_p010_b011 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb12 : c.val < 25
    · exact wide_coarse_distinct_p010_b012 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb13 : c.val < 26
    · exact coarse_distinct_p010_b013 p hpa hpb c (by omega) hb13 hn63 hn87 X hX
    by_cases hb14 : c.val < 27
    · exact coarse_distinct_p010_b014 p hpa hpb c (by omega) hb14 hn63 hn87 X hX
    by_cases hb15 : c.val < 28
    · exact wide_coarse_distinct_p010_b015 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb16 : c.val < 29
    · exact wide_coarse_distinct_p010_b016 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb17 : c.val < 30
    · exact wide_coarse_distinct_p010_b017 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb18 : c.val < 32
    · exact wide_coarse_distinct_p010_b018 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb19 : c.val < 34
    · exact wide_coarse_distinct_p010_b019 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb20 : c.val < 37
    · exact wide_coarse_distinct_p010_b020 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb21 : c.val < 38
    · exact wide_coarse_distinct_p010_b021 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb22 : c.val < 41
    · exact wide_coarse_distinct_p010_b022 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb23 : c.val < 43
    · exact wide_coarse_distinct_p010_b023 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb24 : c.val < 44
    · exact coarse_distinct_p010_b024 p hpa hpb c (by omega) hb24 hn63 hn87 X hX
    by_cases hb25 : c.val < 46
    · exact coarse_distinct_p010_b025 p hpa hpb c (by omega) hb25 hn63 hn87 X hX
    by_cases hb26 : c.val < 54
    · exact coarse_distinct_p010_b026 p hpa hpb c (by omega) hb26 hn63 hn87 X hX
    by_cases hb27 : c.val < 62
    · exact coarse_distinct_p010_b027 p hpa hpb c (by omega) hb27 hn63 hn87 X hX
    by_cases hb28 : c.val < 66
    · exact coarse_distinct_p010_b028 p hpa hpb c (by omega) hb28 hn63 hn87 X hX
    by_cases hb29 : c.val < 68
    · exact coarse_distinct_p010_b029 p hpa hpb c (by omega) hb29 hn63 hn87 X hX
    by_cases hb30 : c.val < 69
    · exact coarse_distinct_p010_b030 p hpa hpb c (by omega) hb30 hn63 hn87 X hX
    by_cases hb31 : c.val < 71
    · exact coarse_distinct_p010_b031 p hpa hpb c (by omega) hb31 hn63 hn87 X hX
    by_cases hb32 : c.val < 73
    · exact coarse_distinct_p010_b032 p hpa hpb c (by omega) hb32 hn63 hn87 X hX
    by_cases hb33 : c.val < 78
    · exact coarse_distinct_p010_b033 p hpa hpb c (by omega) hb33 hn63 hn87 X hX
    by_cases hb34 : c.val < 79
    · exact coarse_distinct_p010_b034 p hpa hpb c (by omega) hb34 hn63 hn87 X hX
    by_cases hb35 : c.val < 81
    · exact coarse_distinct_p010_b035 p hpa hpb c (by omega) hb35 hn63 hn87 X hX
    by_cases hb36 : c.val < 85
    · exact coarse_distinct_p010_b036 p hpa hpb c (by omega) hb36 hn63 hn87 X hX
    exact coarse_distinct_p010_b037 p hpa hpb c (by omega) (by omega) hn63 hn87 X hX
  have hp : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X,
      OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (fun _ _ => true) →
      ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
    intro c hc
    rcases hc with rfl|rfl
    · exact coarse_distinct_p010_positive63 p hpa hpb
    · exact coarse_distinct_p010_positive87 p hpa hpb
  exact ⟨distinct_chart_positive_of_cases p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) hex,
    positive_chart_ratio_of_cases p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) hp⟩

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) :
    (∀ X orders signs, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p010 p hpa hpb

#print axioms solution
