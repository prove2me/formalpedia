-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p013_b028
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T06:21:47.357661+00:00
-- url     : https://prove2.me/submissions/aae5fb72-77b3-4101-bc8d-41013020fccf

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313069_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313069_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313070_s0
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6
theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 71)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 ∨ c=70 := by omega
  rcases hc with rfl|rfl
  · have h0 := collision_c313069_s0 p hpa hpb X hX
    exact collision_c313069_s1 p hpa hpb X hX h0
  · exact collision_c313070_s0 p hpa hpb X hX

#print axioms solution
