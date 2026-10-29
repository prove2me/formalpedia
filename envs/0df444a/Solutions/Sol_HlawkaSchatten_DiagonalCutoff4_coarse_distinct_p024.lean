-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:55:28.808035+00:00
-- url     : https://prove2.me/submissions/f5305fdf-170d-452b-8476-f55d17289d4d

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b038
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b039
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b040
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b041
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b042
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b043
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_b044
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_positive63
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p024_positive87
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_distinct_chart_positive_of_cases
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_positive_chart_ratio_of_cases
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p024 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) :
    (∀ X orders signs, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  have hex : ∀ c : Fin 88, c ≠ 63 → c ≠ 87 → ∀ X, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (distinctSigns c) → False := by
    intro c hn63 hn87 X hX
    by_cases hb0 : c.val < 3
    · exact coarse_distinct_p024_b000 p hpa hpb c (by omega) hb0 hn63 hn87 X hX
    by_cases hb1 : c.val < 6
    · exact wide_coarse_distinct_p023_b001 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb2 : c.val < 9
    · exact coarse_distinct_p024_b002 p hpa hpb c (by omega) hb2 hn63 hn87 X hX
    by_cases hb3 : c.val < 11
    · exact coarse_distinct_p024_b003 p hpa hpb c (by omega) hb3 hn63 hn87 X hX
    by_cases hb4 : c.val < 13
    · exact wide_coarse_distinct_p023_b004 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb5 : c.val < 15
    · exact coarse_distinct_p024_b005 p hpa hpb c (by omega) hb5 hn63 hn87 X hX
    by_cases hb6 : c.val < 17
    · exact wide_coarse_distinct_p023_b006 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb7 : c.val < 19
    · exact wide_coarse_distinct_p023_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb8 : c.val < 21
    · exact coarse_distinct_p024_b008 p hpa hpb c (by omega) hb8 hn63 hn87 X hX
    by_cases hb9 : c.val < 23
    · exact coarse_distinct_p024_b009 p hpa hpb c (by omega) hb9 hn63 hn87 X hX
    by_cases hb10 : c.val < 25
    · exact coarse_distinct_p024_b010 p hpa hpb c (by omega) hb10 hn63 hn87 X hX
    by_cases hb11 : c.val < 27
    · exact wide_coarse_distinct_p023_b012 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb12 : c.val < 29
    · exact coarse_distinct_p024_b012 p hpa hpb c (by omega) hb12 hn63 hn87 X hX
    by_cases hb13 : c.val < 31
    · exact coarse_distinct_p024_b013 p hpa hpb c (by omega) hb13 hn63 hn87 X hX
    by_cases hb14 : c.val < 33
    · exact coarse_distinct_p024_b014 p hpa hpb c (by omega) hb14 hn63 hn87 X hX
    by_cases hb15 : c.val < 36
    · exact coarse_distinct_p024_b015 p hpa hpb c (by omega) hb15 hn63 hn87 X hX
    by_cases hb16 : c.val < 37
    · exact coarse_distinct_p024_b016 p hpa hpb c (by omega) hb16 hn63 hn87 X hX
    by_cases hb17 : c.val < 38
    · exact coarse_distinct_p024_b017 p hpa hpb c (by omega) hb17 hn63 hn87 X hX
    by_cases hb18 : c.val < 39
    · exact coarse_distinct_p024_b018 p hpa hpb c (by omega) hb18 hn63 hn87 X hX
    by_cases hb19 : c.val < 41
    · exact coarse_distinct_p024_b019 p hpa hpb c (by omega) hb19 hn63 hn87 X hX
    by_cases hb20 : c.val < 44
    · exact wide_coarse_distinct_p023_b022 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb21 : c.val < 45
    · exact coarse_distinct_p024_b021 p hpa hpb c (by omega) hb21 hn63 hn87 X hX
    by_cases hb22 : c.val < 47
    · exact wide_coarse_distinct_p023_b024 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb23 : c.val < 48
    · exact wide_coarse_distinct_p023_b025 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb24 : c.val < 49
    · exact wide_coarse_distinct_p023_b026 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb25 : c.val < 50
    · exact coarse_distinct_p024_b025 p hpa hpb c (by omega) hb25 hn63 hn87 X hX
    by_cases hb26 : c.val < 51
    · exact coarse_distinct_p024_b026 p hpa hpb c (by omega) hb26 hn63 hn87 X hX
    by_cases hb27 : c.val < 52
    · exact wide_coarse_distinct_p023_b029 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) hn63 hn87 X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb28 : c.val < 56
    · exact coarse_distinct_p024_b028 p hpa hpb c (by omega) hb28 hn63 hn87 X hX
    by_cases hb29 : c.val < 57
    · exact coarse_distinct_p024_b029 p hpa hpb c (by omega) hb29 hn63 hn87 X hX
    by_cases hb30 : c.val < 58
    · exact coarse_distinct_p024_b030 p hpa hpb c (by omega) hb30 hn63 hn87 X hX
    by_cases hb31 : c.val < 59
    · exact coarse_distinct_p024_b031 p hpa hpb c (by omega) hb31 hn63 hn87 X hX
    by_cases hb32 : c.val < 60
    · exact coarse_distinct_p024_b032 p hpa hpb c (by omega) hb32 hn63 hn87 X hX
    by_cases hb33 : c.val < 65
    · exact coarse_distinct_p024_b033 p hpa hpb c (by omega) hb33 hn63 hn87 X hX
    by_cases hb34 : c.val < 68
    · exact coarse_distinct_p024_b034 p hpa hpb c (by omega) hb34 hn63 hn87 X hX
    by_cases hb35 : c.val < 70
    · exact coarse_distinct_p024_b035 p hpa hpb c (by omega) hb35 hn63 hn87 X hX
    by_cases hb36 : c.val < 72
    · exact coarse_distinct_p024_b036 p hpa hpb c (by omega) hb36 hn63 hn87 X hX
    by_cases hb37 : c.val < 75
    · exact coarse_distinct_p024_b037 p hpa hpb c (by omega) hb37 hn63 hn87 X hX
    by_cases hb38 : c.val < 76
    · exact coarse_distinct_p024_b038 p hpa hpb c (by omega) hb38 hn63 hn87 X hX
    by_cases hb39 : c.val < 78
    · exact coarse_distinct_p024_b039 p hpa hpb c (by omega) hb39 hn63 hn87 X hX
    by_cases hb40 : c.val < 80
    · exact coarse_distinct_p024_b040 p hpa hpb c (by omega) hb40 hn63 hn87 X hX
    by_cases hb41 : c.val < 82
    · exact coarse_distinct_p024_b041 p hpa hpb c (by omega) hb41 hn63 hn87 X hX
    by_cases hb42 : c.val < 83
    · exact coarse_distinct_p024_b042 p hpa hpb c (by omega) hb42 hn63 hn87 X hX
    by_cases hb43 : c.val < 85
    · exact coarse_distinct_p024_b043 p hpa hpb c (by omega) hb43 hn63 hn87 X hX
    exact coarse_distinct_p024_b044 p hpa hpb c (by omega) (by omega) hn63 hn87 X hX
  have hp : ∀ c : Fin 88, c=63 ∨ c=87 → ∀ X,
      OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X (distinctOrders c) (fun _ _ => true) →
      ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by
    intro c hc
    rcases hc with rfl|rfl
    · exact coarse_distinct_p024_positive63 p hpa hpb
    · exact coarse_distinct_p024_positive87 p hpa hpb
  exact ⟨distinct_chart_positive_of_cases p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) hex,
    positive_chart_ratio_of_cases p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) hp⟩

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ)) :
    (∀ X orders signs, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X orders signs →
      (∀ h, signs 0 h=true) → (∀ j, orders j 0=j) → signs=(fun _ _ => true)) ∧
    (∀ X orders, OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X orders (fun _ _ => true) →
      (∀ j, orders j 0=j) → ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p024 p hpa hpb

#print axioms solution
