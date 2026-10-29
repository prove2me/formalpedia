-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:11:39.747005+00:00
-- url     : https://prove2.me/submissions/785ff507-6e75-419b-bd69-dd9743a6d6c6

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p007_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p005_b017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p004_b024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p006_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b038
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_b039
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_positive63
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_positive87
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_chart_positive_of_cases
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio_of_cases
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p007 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) :
    (∀ X orders signs, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  have hex : ∀ c : Fin 88, c ≠ 63 → c ≠ 87 → ∀ X, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (distinctSigns c) → False := by
    intro c hn63 hn87 X hX
    by_cases hb0 : c.val < 3
    · exact wide_coarse_distinct_p004_b000 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb1 : c.val < 5
    · exact wide_coarse_distinct_p004_b001 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb2 : c.val < 7
    · exact wide_coarse_distinct_p004_b002 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb3 : c.val < 9
    · exact wide_coarse_distinct_p004_b003 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb4 : c.val < 11
    · exact wide_coarse_distinct_p004_b004 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb5 : c.val < 12
    · exact wide_coarse_distinct_p004_b005 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb6 : c.val < 15
    · exact wide_coarse_distinct_p004_b006 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb7 : c.val < 17
    · exact wide_coarse_distinct_p007_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb8 : c.val < 18
    · exact wide_coarse_distinct_p004_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb9 : c.val < 19
    · exact wide_coarse_distinct_p004_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb10 : c.val < 20
    · exact wide_coarse_distinct_p004_b008 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb11 : c.val < 21
    · exact wide_coarse_distinct_p004_b009 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb12 : c.val < 22
    · exact wide_coarse_distinct_p004_b010 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb13 : c.val < 25
    · exact wide_coarse_distinct_p004_b011 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb14 : c.val < 26
    · exact wide_coarse_distinct_p004_b012 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb15 : c.val < 27
    · exact wide_coarse_distinct_p004_b013 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb16 : c.val < 28
    · exact wide_coarse_distinct_p004_b013 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb17 : c.val < 29
    · exact wide_coarse_distinct_p004_b014 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb18 : c.val < 30
    · exact wide_coarse_distinct_p004_b015 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb19 : c.val < 32
    · exact wide_coarse_distinct_p004_b016 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb20 : c.val < 34
    · exact wide_coarse_distinct_p005_b017 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb21 : c.val < 37
    · exact wide_coarse_distinct_p004_b019 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb22 : c.val < 38
    · exact wide_coarse_distinct_p004_b020 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb23 : c.val < 41
    · exact wide_coarse_distinct_p004_b021 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb24 : c.val < 43
    · exact wide_coarse_distinct_p004_b022 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb25 : c.val < 44
    · exact wide_coarse_distinct_p004_b023 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb26 : c.val < 46
    · exact wide_coarse_distinct_p004_b024 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb27 : c.val < 54
    · exact wide_coarse_distinct_p006_b025 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb28 : c.val < 62
    · exact coarse_distinct_p007_b028 p hpa hpb c (by omega) hb28 hn63 hn87 X hX
    by_cases hb29 : c.val < 66
    · exact coarse_distinct_p007_b029 p hpa hpb c (by omega) hb29 hn63 hn87 X hX
    by_cases hb30 : c.val < 68
    · exact coarse_distinct_p007_b030 p hpa hpb c (by omega) hb30 hn63 hn87 X hX
    by_cases hb31 : c.val < 69
    · exact coarse_distinct_p007_b031 p hpa hpb c (by omega) hb31 hn63 hn87 X hX
    by_cases hb32 : c.val < 70
    · exact coarse_distinct_p007_b032 p hpa hpb c (by omega) hb32 hn63 hn87 X hX
    by_cases hb33 : c.val < 71
    · exact coarse_distinct_p007_b033 p hpa hpb c (by omega) hb33 hn63 hn87 X hX
    by_cases hb34 : c.val < 73
    · exact coarse_distinct_p007_b034 p hpa hpb c (by omega) hb34 hn63 hn87 X hX
    by_cases hb35 : c.val < 78
    · exact coarse_distinct_p007_b035 p hpa hpb c (by omega) hb35 hn63 hn87 X hX
    by_cases hb36 : c.val < 79
    · exact coarse_distinct_p007_b036 p hpa hpb c (by omega) hb36 hn63 hn87 X hX
    by_cases hb37 : c.val < 81
    · exact coarse_distinct_p007_b037 p hpa hpb c (by omega) hb37 hn63 hn87 X hX
    by_cases hb38 : c.val < 85
    · exact coarse_distinct_p007_b038 p hpa hpb c (by omega) hb38 hn63 hn87 X hX
    exact coarse_distinct_p007_b039 p hpa hpb c (by omega) (by omega) hn63 hn87 X hX
  have hp : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X,
      OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders c) (fun _ _ => true) →
      ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
    intro c hc
    rcases hc with rfl|rfl
    · exact coarse_distinct_p007_positive63 p hpa hpb
    · exact coarse_distinct_p007_positive87 p hpa hpb
  exact ⟨distinct_chart_positive_of_cases p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) hex,
    positive_chart_ratio_of_cases p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) hp⟩

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) :
    (∀ X orders signs, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007 p hpa hpb

#print axioms solution
