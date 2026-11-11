-- Prove2me | solution 1 for OAI.SharpPlanar.Bernstein4.N1_right.bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:53:02.01962+00:00
-- url     : https://prove2.me/submissions/6c259424-5bac-4f91-bfae-ad33a6caed20

import Mathlib
import Definitions.Def_OAIQ098G382
import Definitions.Def_OAIQ098G1653
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1690
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t0_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t10_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t11_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t12_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t13_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t14_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t15_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t16_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t17_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t1_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t2_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t3_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t4_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t5_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t6_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t7_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t8_contains_g
import Theorems.Thm_OAI_SharpPlanar_Bernstein4_N1_right_t9_contains_g
import Theorems.Thm_OAI_SharpPlanar_RBox_contains_of_abs_g
import Theorems.Thm_OAI_SharpPlanar_RBox_lower_lt_g
import Theorems.Thm_OAI_SharpPlanar_bernsteinBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_sourcePower_of_cap_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_CoarseBound4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma coarse_4_20 : sharpTaylor 20 4/((Nat.factorial 20):ℝ)≤(17856764703442514988652965:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_21 : sharpTaylor 21 4/((Nat.factorial 21):ℝ)≤(4795198285550590272913451:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_22 : sharpTaylor 22 4/((Nat.factorial 22):ℝ)≤(1254256646504824911026482:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_23 : sharpTaylor 23 4/((Nat.factorial 23):ℝ)≤(320177663759881569024883:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_24 : sharpTaylor 24 4/((Nat.factorial 24):ℝ)≤(79894005576595043659965:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_25 : sharpTaylor 25 4/((Nat.factorial 25):ℝ)≤(19511828237460268174178:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_26 : sharpTaylor 26 4/((Nat.factorial 26):ℝ)≤(4668108418516200862028:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_27 : sharpTaylor 27 4/((Nat.factorial 27):ℝ)≤(1094743085585397964913:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_28 : sharpTaylor 28 4/((Nat.factorial 28):ℝ)≤(251750894163451011458:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_29 : sharpTaylor 29 4/((Nat.factorial 29):ℝ)≤(56779405902779528581:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
lemma coarse_4_30 : sharpTaylor 30 4/((Nat.factorial 30):ℝ)≤(12559896881259635565:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein4
open IntegerIntervals IntegerBasis Numerical CachedData
namespace N1_right
lemma t18_contains : t18.Contains (sourcePower true 4 (3/2) 2 18) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 18 coarse_4_20) <;> norm_num [t18,precision]
lemma t19_contains : t19.Contains (sourcePower true 4 (3/2) 2 19) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 19 coarse_4_21) <;> norm_num [t19,precision]
lemma t20_contains : t20.Contains (sourcePower true 4 (3/2) 2 20) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 20 coarse_4_22) <;> norm_num [t20,precision]
lemma t21_contains : t21.Contains (sourcePower true 4 (3/2) 2 21) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 21 coarse_4_23) <;> norm_num [t21,precision]
lemma t22_contains : t22.Contains (sourcePower true 4 (3/2) 2 22) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 22 coarse_4_24) <;> norm_num [t22,precision]
lemma t23_contains : t23.Contains (sourcePower true 4 (3/2) 2 23) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 23 coarse_4_25) <;> norm_num [t23,precision]
lemma t24_contains : t24.Contains (sourcePower true 4 (3/2) 2 24) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 24 coarse_4_26) <;> norm_num [t24,precision]
lemma t25_contains : t25.Contains (sourcePower true 4 (3/2) 2 25) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 25 coarse_4_27) <;> norm_num [t25,precision]
lemma t26_contains : t26.Contains (sourcePower true 4 (3/2) 2 26) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 26 coarse_4_28) <;> norm_num [t26,precision]
lemma t27_contains : t27.Contains (sourcePower true 4 (3/2) 2 27) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 27 coarse_4_29) <;> norm_num [t27,precision]
lemma t28_contains : t28.Contains (sourcePower true 4 (3/2) 2 28) := by
  apply RBox.contains_of_abs_g (sourcePower_of_cap_g true 4 (3/2) 2 28 coarse_4_30) <;> norm_num [t28,precision]
lemma ts_contains (r : Fin 29) : (ts r).Contains (sourcePower true 4 (3/2) 2 r.val) := by
  fin_cases r
  · exact t0_contains_g
  · exact t1_contains_g
  · exact t2_contains_g
  · exact t3_contains_g
  · exact t4_contains_g
  · exact t5_contains_g
  · exact t6_contains_g
  · exact t7_contains_g
  · exact t8_contains_g
  · exact t9_contains_g
  · exact t10_contains_g
  · exact t11_contains_g
  · exact t12_contains_g
  · exact t13_contains_g
  · exact t14_contains_g
  · exact t15_contains_g
  · exact t16_contains_g
  · exact t17_contains_g
  · exact t18_contains
  · exact t19_contains
  · exact t20_contains
  · exact t21_contains
  · exact t22_contains
  · exact t23_contains
  · exact t24_contains
  · exact t25_contains
  · exact t26_contains
  · exact t27_contains
  · exact t28_contains
lemma bound0 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 0 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨0,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound1 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 1 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨1,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound2 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 2 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨2,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound3 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 3 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨3,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound4 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 4 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨4,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound5 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 5 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨5,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound6 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 6 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨6,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound7 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 7 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨7,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound8 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 8 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨8,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound9 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 9 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨9,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound10 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 10 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨10,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound11 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 11 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨11,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound12 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 12 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨12,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound13 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 13 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨13,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound14 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 14 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨14,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound15 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 15 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨15,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound16 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 16 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨16,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound17 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 17 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨17,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound18 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 18 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨18,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound19 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 19 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨19,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound20 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 20 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨20,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound21 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 21 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨21,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound22 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 22 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨22,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound23 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 23 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨23,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound24 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 24 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨24,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound25 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 25 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨25,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound26 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 26 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨26,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound27 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 27 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨27,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound28 : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) 28 := by
  simpa only [Int.cast_ofNat,Int.cast_one] using RBox.lower_lt_g (u := 1) (v := 50) (bernsteinBox_contains_g ts_contains ⟨28,by norm_num⟩) (by norm_num : (0:ℤ)<50) (by decide +kernel)
lemma bound_g_oai (k : Fin 29) : (1:ℝ)/50<powerToBernstein 28 (sourcePower true 4 (3/2) 2) k.val := by
  fin_cases k
  · exact bound0
  · exact bound1
  · exact bound2
  · exact bound3
  · exact bound4
  · exact bound5
  · exact bound6
  · exact bound7
  · exact bound8
  · exact bound9
  · exact bound10
  · exact bound11
  · exact bound12
  · exact bound13
  · exact bound14
  · exact bound15
  · exact bound16
  · exact bound17
  · exact bound18
  · exact bound19
  · exact bound20
  · exact bound21
  · exact bound22
  · exact bound23
  · exact bound24
  · exact bound25
  · exact bound26
  · exact bound27
  · exact bound28
end N1_right
end SharpPlanar.Bernstein4

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Bernstein4.N1_right.bound_g_oai := @OAI.SharpPlanar.Bernstein4.N1_right.bound_g_oai
