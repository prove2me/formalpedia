-- Prove2me | solution 1 for HlawkaSchatten.DiagonalBelow16.cutoff255over16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:54:56.9679+00:00
-- url     : https://prove2.me/submissions/8dbc1de5-227d-461a-a3b3-dc8a59266dc7

import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w000_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w001_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w002_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s000_001
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s002_003
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s004_005
import Theorems.Thm_HlawkaSchatten_DiagonalBelow16_real_three_w003_s006_007
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_complex_least_of_real_three
import Mathlib.Tactic.Linarith
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, (255/16 : ℝ) ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by
  intro p hp
  by_cases h16 : 16 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.cutoff16 p h16
  apply HlawkaSchatten.DiagonalCutoff21.complex_least_of_real_three p (by linarith)
  by_cases hb0 : p ≤ (4081/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s000_001 p (by linarith) hb0
  by_cases hb1 : p ≤ (2041/128 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s002_003 p (by linarith) hb1
  by_cases hb2 : p ≤ (4083/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s004_005 p (by linarith) hb2
  by_cases hb3 : p ≤ (1021/64 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w000_s006_007 p (by linarith) hb3
  by_cases hb4 : p ≤ (4085/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w001_s000_001 p (by linarith) hb4
  by_cases hb5 : p ≤ (2043/128 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w001_s002_003 p (by linarith) hb5
  by_cases hb6 : p ≤ (4087/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w001_s004_005 p (by linarith) hb6
  by_cases hb7 : p ≤ (511/32 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w001_s006_007 p (by linarith) hb7
  by_cases hb8 : p ≤ (4089/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s000_001 p (by linarith) hb8
  by_cases hb9 : p ≤ (2045/128 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s002_003 p (by linarith) hb9
  by_cases hb10 : p ≤ (4091/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s004_005 p (by linarith) hb10
  by_cases hb11 : p ≤ (1023/64 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w002_s006_007 p (by linarith) hb11
  by_cases hb12 : p ≤ (4093/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s000_001 p (by linarith) hb12
  by_cases hb13 : p ≤ (2047/128 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s002_003 p (by linarith) hb13
  by_cases hb14 : p ≤ (4095/256 : ℝ)
  · exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s004_005 p (by linarith) hb14
  exact HlawkaSchatten.DiagonalBelow16.real_three_w003_s006_007 p (by linarith) (by linarith)

#print axioms solution
