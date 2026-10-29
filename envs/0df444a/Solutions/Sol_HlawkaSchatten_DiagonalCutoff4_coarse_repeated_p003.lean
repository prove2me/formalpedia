-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:17:19.402387+00:00
-- url     : https://prove2.me/submissions/7bde0b0f-1b9f-4ba3-9eae-a9be246b24c0

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_chart_weaken_parameters
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b000
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b001
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b002
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b003
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b004
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b005
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b006
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b008
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b009
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b010
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b011
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b012
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b013
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b014
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b015
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b016
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b017
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b018
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b019
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b020
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b021
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b022
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b023
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b024
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b025
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b026
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b027
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b028
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b029
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b030
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b031
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b032
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b033
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b034
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b035
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b036
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b037
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b038
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b039
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b040
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b041
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b042
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b043
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b044
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b045
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b046
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b047
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b048
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b049
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b050
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b051
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b052
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b053
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b054
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b055
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b056
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b057
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b058
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b059
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b060
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b061
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b062
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b063
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b064
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b065
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b066
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b067
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b068
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b069
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b070
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b071
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b072
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b073
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b074
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b075
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b076
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b077
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b078
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b079
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b080
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b081
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b082
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b083
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b084
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b085
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b086
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b087
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b088
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b089
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b090
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b091
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b092
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b093
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b094
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b095
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b096
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b097
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_supportfree_repeated_b098
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b099
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b100
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b101
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b102
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b103
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b104
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b105
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b106
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_repeated_p003_b107
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_main_injective_of_cases
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_repeated_p003 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) :
    ∀ X orders signs, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  have hex : ∀ c : Fin 323, ∀ X, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (repeatedOrders c) (repeatedSigns c) → False := by
    intro c X hX
    by_cases hb0 : c.val < 3
    · exact supportfree_repeated_b000 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb1 : c.val < 6
    · exact supportfree_repeated_b001 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb2 : c.val < 9
    · exact supportfree_repeated_b002 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb3 : c.val < 12
    · exact supportfree_repeated_b003 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb4 : c.val < 15
    · exact supportfree_repeated_b004 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb5 : c.val < 18
    · exact supportfree_repeated_b005 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb6 : c.val < 21
    · exact supportfree_repeated_b006 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb7 : c.val < 24
    · exact supportfree_repeated_b007 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb8 : c.val < 27
    · exact supportfree_repeated_b008 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb9 : c.val < 30
    · exact supportfree_repeated_b009 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb10 : c.val < 33
    · exact supportfree_repeated_b010 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb11 : c.val < 36
    · exact supportfree_repeated_b011 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb12 : c.val < 39
    · exact supportfree_repeated_b012 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb13 : c.val < 42
    · exact supportfree_repeated_b013 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb14 : c.val < 45
    · exact supportfree_repeated_b014 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb15 : c.val < 48
    · exact supportfree_repeated_b015 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb16 : c.val < 51
    · exact supportfree_repeated_b016 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb17 : c.val < 54
    · exact coarse_repeated_p003_b017 p hpa hpb c (by omega) hb17 X hX
    by_cases hb18 : c.val < 57
    · exact coarse_repeated_p003_b018 p hpa hpb c (by omega) hb18 X hX
    by_cases hb19 : c.val < 60
    · exact supportfree_repeated_b019 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb20 : c.val < 63
    · exact coarse_repeated_p003_b020 p hpa hpb c (by omega) hb20 X hX
    by_cases hb21 : c.val < 66
    · exact supportfree_repeated_b021 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb22 : c.val < 69
    · exact coarse_repeated_p003_b022 p hpa hpb c (by omega) hb22 X hX
    by_cases hb23 : c.val < 72
    · exact coarse_repeated_p003_b023 p hpa hpb c (by omega) hb23 X hX
    by_cases hb24 : c.val < 75
    · exact coarse_repeated_p003_b024 p hpa hpb c (by omega) hb24 X hX
    by_cases hb25 : c.val < 78
    · exact coarse_repeated_p003_b025 p hpa hpb c (by omega) hb25 X hX
    by_cases hb26 : c.val < 81
    · exact coarse_repeated_p003_b026 p hpa hpb c (by omega) hb26 X hX
    by_cases hb27 : c.val < 84
    · exact coarse_repeated_p003_b027 p hpa hpb c (by omega) hb27 X hX
    by_cases hb28 : c.val < 87
    · exact coarse_repeated_p003_b028 p hpa hpb c (by omega) hb28 X hX
    by_cases hb29 : c.val < 90
    · exact coarse_repeated_p003_b029 p hpa hpb c (by omega) hb29 X hX
    by_cases hb30 : c.val < 93
    · exact coarse_repeated_p003_b030 p hpa hpb c (by omega) hb30 X hX
    by_cases hb31 : c.val < 96
    · exact supportfree_repeated_b031 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb32 : c.val < 99
    · exact coarse_repeated_p003_b032 p hpa hpb c (by omega) hb32 X hX
    by_cases hb33 : c.val < 102
    · exact supportfree_repeated_b033 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb34 : c.val < 105
    · exact coarse_repeated_p003_b034 p hpa hpb c (by omega) hb34 X hX
    by_cases hb35 : c.val < 108
    · exact coarse_repeated_p003_b035 p hpa hpb c (by omega) hb35 X hX
    by_cases hb36 : c.val < 111
    · exact coarse_repeated_p003_b036 p hpa hpb c (by omega) hb36 X hX
    by_cases hb37 : c.val < 114
    · exact coarse_repeated_p003_b037 p hpa hpb c (by omega) hb37 X hX
    by_cases hb38 : c.val < 117
    · exact coarse_repeated_p003_b038 p hpa hpb c (by omega) hb38 X hX
    by_cases hb39 : c.val < 120
    · exact coarse_repeated_p003_b039 p hpa hpb c (by omega) hb39 X hX
    by_cases hb40 : c.val < 123
    · exact coarse_repeated_p003_b040 p hpa hpb c (by omega) hb40 X hX
    by_cases hb41 : c.val < 126
    · exact coarse_repeated_p003_b041 p hpa hpb c (by omega) hb41 X hX
    by_cases hb42 : c.val < 129
    · exact supportfree_repeated_b042 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb43 : c.val < 132
    · exact coarse_repeated_p003_b043 p hpa hpb c (by omega) hb43 X hX
    by_cases hb44 : c.val < 135
    · exact coarse_repeated_p003_b044 p hpa hpb c (by omega) hb44 X hX
    by_cases hb45 : c.val < 138
    · exact supportfree_repeated_b045 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb46 : c.val < 141
    · exact coarse_repeated_p003_b046 p hpa hpb c (by omega) hb46 X hX
    by_cases hb47 : c.val < 144
    · exact coarse_repeated_p003_b047 p hpa hpb c (by omega) hb47 X hX
    by_cases hb48 : c.val < 147
    · exact coarse_repeated_p003_b048 p hpa hpb c (by omega) hb48 X hX
    by_cases hb49 : c.val < 150
    · exact supportfree_repeated_b049 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb50 : c.val < 153
    · exact coarse_repeated_p003_b050 p hpa hpb c (by omega) hb50 X hX
    by_cases hb51 : c.val < 156
    · exact coarse_repeated_p003_b051 p hpa hpb c (by omega) hb51 X hX
    by_cases hb52 : c.val < 159
    · exact supportfree_repeated_b052 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb53 : c.val < 162
    · exact coarse_repeated_p003_b053 p hpa hpb c (by omega) hb53 X hX
    by_cases hb54 : c.val < 165
    · exact coarse_repeated_p003_b054 p hpa hpb c (by omega) hb54 X hX
    by_cases hb55 : c.val < 168
    · exact coarse_repeated_p003_b055 p hpa hpb c (by omega) hb55 X hX
    by_cases hb56 : c.val < 171
    · exact coarse_repeated_p003_b056 p hpa hpb c (by omega) hb56 X hX
    by_cases hb57 : c.val < 174
    · exact coarse_repeated_p003_b057 p hpa hpb c (by omega) hb57 X hX
    by_cases hb58 : c.val < 177
    · exact coarse_repeated_p003_b058 p hpa hpb c (by omega) hb58 X hX
    by_cases hb59 : c.val < 180
    · exact coarse_repeated_p003_b059 p hpa hpb c (by omega) hb59 X hX
    by_cases hb60 : c.val < 183
    · exact coarse_repeated_p003_b060 p hpa hpb c (by omega) hb60 X hX
    by_cases hb61 : c.val < 186
    · exact coarse_repeated_p003_b061 p hpa hpb c (by omega) hb61 X hX
    by_cases hb62 : c.val < 189
    · exact coarse_repeated_p003_b062 p hpa hpb c (by omega) hb62 X hX
    by_cases hb63 : c.val < 192
    · exact supportfree_repeated_b063 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb64 : c.val < 195
    · exact coarse_repeated_p003_b064 p hpa hpb c (by omega) hb64 X hX
    by_cases hb65 : c.val < 198
    · exact coarse_repeated_p003_b065 p hpa hpb c (by omega) hb65 X hX
    by_cases hb66 : c.val < 201
    · exact supportfree_repeated_b066 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb67 : c.val < 204
    · exact coarse_repeated_p003_b067 p hpa hpb c (by omega) hb67 X hX
    by_cases hb68 : c.val < 207
    · exact coarse_repeated_p003_b068 p hpa hpb c (by omega) hb68 X hX
    by_cases hb69 : c.val < 210
    · exact coarse_repeated_p003_b069 p hpa hpb c (by omega) hb69 X hX
    by_cases hb70 : c.val < 213
    · exact coarse_repeated_p003_b070 p hpa hpb c (by omega) hb70 X hX
    by_cases hb71 : c.val < 216
    · exact coarse_repeated_p003_b071 p hpa hpb c (by omega) hb71 X hX
    by_cases hb72 : c.val < 219
    · exact coarse_repeated_p003_b072 p hpa hpb c (by omega) hb72 X hX
    by_cases hb73 : c.val < 222
    · exact supportfree_repeated_b073 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb74 : c.val < 225
    · exact coarse_repeated_p003_b074 p hpa hpb c (by omega) hb74 X hX
    by_cases hb75 : c.val < 228
    · exact coarse_repeated_p003_b075 p hpa hpb c (by omega) hb75 X hX
    by_cases hb76 : c.val < 231
    · exact coarse_repeated_p003_b076 p hpa hpb c (by omega) hb76 X hX
    by_cases hb77 : c.val < 234
    · exact coarse_repeated_p003_b077 p hpa hpb c (by omega) hb77 X hX
    by_cases hb78 : c.val < 237
    · exact coarse_repeated_p003_b078 p hpa hpb c (by omega) hb78 X hX
    by_cases hb79 : c.val < 240
    · exact coarse_repeated_p003_b079 p hpa hpb c (by omega) hb79 X hX
    by_cases hb80 : c.val < 243
    · exact coarse_repeated_p003_b080 p hpa hpb c (by omega) hb80 X hX
    by_cases hb81 : c.val < 246
    · exact coarse_repeated_p003_b081 p hpa hpb c (by omega) hb81 X hX
    by_cases hb82 : c.val < 249
    · exact coarse_repeated_p003_b082 p hpa hpb c (by omega) hb82 X hX
    by_cases hb83 : c.val < 252
    · exact coarse_repeated_p003_b083 p hpa hpb c (by omega) hb83 X hX
    by_cases hb84 : c.val < 255
    · exact coarse_repeated_p003_b084 p hpa hpb c (by omega) hb84 X hX
    by_cases hb85 : c.val < 258
    · exact coarse_repeated_p003_b085 p hpa hpb c (by omega) hb85 X hX
    by_cases hb86 : c.val < 261
    · exact supportfree_repeated_b086 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb87 : c.val < 264
    · exact coarse_repeated_p003_b087 p hpa hpb c (by omega) hb87 X hX
    by_cases hb88 : c.val < 267
    · exact coarse_repeated_p003_b088 p hpa hpb c (by omega) hb88 X hX
    by_cases hb89 : c.val < 270
    · exact coarse_repeated_p003_b089 p hpa hpb c (by omega) hb89 X hX
    by_cases hb90 : c.val < 273
    · exact coarse_repeated_p003_b090 p hpa hpb c (by omega) hb90 X hX
    by_cases hb91 : c.val < 276
    · exact coarse_repeated_p003_b091 p hpa hpb c (by omega) hb91 X hX
    by_cases hb92 : c.val < 279
    · exact coarse_repeated_p003_b092 p hpa hpb c (by omega) hb92 X hX
    by_cases hb93 : c.val < 282
    · exact coarse_repeated_p003_b093 p hpa hpb c (by omega) hb93 X hX
    by_cases hb94 : c.val < 285
    · exact coarse_repeated_p003_b094 p hpa hpb c (by omega) hb94 X hX
    by_cases hb95 : c.val < 288
    · exact coarse_repeated_p003_b095 p hpa hpb c (by omega) hb95 X hX
    by_cases hb96 : c.val < 291
    · exact supportfree_repeated_b096 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb97 : c.val < 294
    · exact coarse_repeated_p003_b097 p hpa hpb c (by omega) hb97 X hX
    by_cases hb98 : c.val < 297
    · exact supportfree_repeated_b098 p (by linarith only [hpa]) (by linarith only [hpb])
        c (by omega) (by omega) X (ordered_chart_weaken_parameters
          (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
    by_cases hb99 : c.val < 300
    · exact coarse_repeated_p003_b099 p hpa hpb c (by omega) hb99 X hX
    by_cases hb100 : c.val < 303
    · exact coarse_repeated_p003_b100 p hpa hpb c (by omega) hb100 X hX
    by_cases hb101 : c.val < 306
    · exact coarse_repeated_p003_b101 p hpa hpb c (by omega) hb101 X hX
    by_cases hb102 : c.val < 309
    · exact coarse_repeated_p003_b102 p hpa hpb c (by omega) hb102 X hX
    by_cases hb103 : c.val < 312
    · exact coarse_repeated_p003_b103 p hpa hpb c (by omega) hb103 X hX
    by_cases hb104 : c.val < 315
    · exact coarse_repeated_p003_b104 p hpa hpb c (by omega) hb104 X hX
    by_cases hb105 : c.val < 318
    · exact coarse_repeated_p003_b105 p hpa hpb c (by omega) hb105 X hX
    by_cases hb106 : c.val < 321
    · exact coarse_repeated_p003_b106 p hpa hpb c (by omega) hb106 X hX
    exact coarse_repeated_p003_b107 p hpa hpb c (by omega) (by omega) X hX
  exact ordered_main_injective_of_cases p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) hex

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) :
    ∀ X orders signs, OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X orders signs → Function.Injective (fun j => orders j 0) := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_repeated_p003 p hpa hpb

#print axioms solution
