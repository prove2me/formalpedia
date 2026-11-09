-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots26_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:16.391176+00:00
-- url     : https://prove2.me/submissions/209569f2-b1df-46d7-99b0-4dd9b254913e

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G053
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G094
import Definitions.Def_OAIQ098G095
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_scale_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_exp_from_horner_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_horner_step_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma power_mul {a b c : CBox} {z : ℂ} {j k : ℕ}
    (ha : a.Contains (z^j)) (hb : b.Contains (z^k)) (hc : a.MulCheck b c) :
    c.Contains (z^(j+k)) := by rw [pow_add]; exact CBox.mul_contains_g ha hb hc


end IntegerIntervals
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar

lemma rootPhase_add (n m : ℕ) : rootPhase (n+m) = rootPhase n*rootPhase m := by
  unfold rootPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


end SharpPlanar

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
lemma fact0_check : fact0.RatCheck 1 1 0 1 := by decide +kernel
lemma fact1_check : fact1.RatCheck 1 1 0 1 := by decide +kernel
lemma fact2_check : fact2.RatCheck 1 2 0 1 := by decide +kernel
lemma fact3_check : fact3.RatCheck 1 6 0 1 := by decide +kernel
lemma fact4_check : fact4.RatCheck 1 24 0 1 := by decide +kernel
lemma fact5_check : fact5.RatCheck 1 120 0 1 := by decide +kernel
lemma fact6_check : fact6.RatCheck 1 720 0 1 := by decide +kernel
lemma fact7_check : fact7.RatCheck 1 5040 0 1 := by decide +kernel
lemma fact8_check : fact8.RatCheck 1 40320 0 1 := by decide +kernel
lemma fact9_check : fact9.RatCheck 1 362880 0 1 := by decide +kernel
lemma fact10_check : fact10.RatCheck 1 3628800 0 1 := by decide +kernel
lemma fact11_check : fact11.RatCheck 1 39916800 0 1 := by decide +kernel
lemma fact12_check : fact12.RatCheck 1 479001600 0 1 := by decide +kernel
lemma fact13_check : fact13.RatCheck 1 6227020800 0 1 := by decide +kernel
lemma fact14_check : fact14.RatCheck 1 87178291200 0 1 := by decide +kernel
lemma fact15_check : fact15.RatCheck 1 1307674368000 0 1 := by decide +kernel
lemma fact16_check : fact16.RatCheck 1 20922789888000 0 1 := by decide +kernel
lemma fact17_check : fact17.RatCheck 1 355687428096000 0 1 := by decide +kernel
lemma fact18_check : fact18.RatCheck 1 6402373705728000 0 1 := by decide +kernel
lemma fact19_check : fact19.RatCheck 1 121645100408832000 0 1 := by decide +kernel
lemma fact20_check : fact20.RatCheck 1 2432902008176640000 0 1 := by decide +kernel
lemma fact21_check : fact21.RatCheck 1 51090942171709440000 0 1 := by decide +kernel
lemma fact22_check : fact22.RatCheck 1 1124000727777607680000 0 1 := by decide +kernel
lemma fact23_check : fact23.RatCheck 1 25852016738884976640000 0 1 := by decide +kernel
lemma fact24_check : fact24.RatCheck 1 620448401733239439360000 0 1 := by decide +kernel
lemma fact25_check : fact25.RatCheck 1 15511210043330985984000000 0 1 := by decide +kernel
lemma fact26_check : fact26.RatCheck 1 403291461126605635584000000 0 1 := by decide +kernel
lemma fact27_check : fact27.RatCheck 1 10888869450418352160768000000 0 1 := by decide +kernel
lemma fact28_check : fact28.RatCheck 1 304888344611713860501504000000 0 1 := by decide +kernel
lemma fact29_check : fact29.RatCheck 1 8841761993739701954543616000000 0 1 := by decide +kernel
lemma fact30_check : fact30.RatCheck 1 265252859812191058636308480000000 0 1 := by decide +kernel
lemma fact31_check : fact31.RatCheck 1 8222838654177922817725562880000000 0 1 := by decide +kernel
lemma fact32_check : fact32.RatCheck 1 263130836933693530167218012160000000 0 1 := by decide +kernel
lemma phaseInput_contains : phaseInput.Contains (Complex.I*Real.pi/512) := by
  constructor
  · norm_num [phaseInput,RBox.Contains,Complex.mul_re,Complex.I_re,Complex.I_im]
  · have hh := RBox.scale_contains_g piBounds_contains_g
      (c:=phaseInput.im) (m:=1) (n:=512) (by decide +kernel)
    simpa [div_eq_mul_inv,mul_comm] using hh
lemma small_contains : small.Contains ((1/2048:ℂ)*(Complex.I*Real.pi/512)) := by
  simpa using CBox.scale_contains_g phaseInput_contains (c:=small) (m:=1) (n:=2048) (by decide +kernel)
lemma h32 : poly32.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 32 0) := by
  simpa [expHorner,poly32,Nat.factorial] using CBox.rat_contains_g fact32_check
lemma h31 : poly31.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 31 1) := by
  exact horner_step_g small_contains h32 fact31_check (m:=mul31) (by decide +kernel) (by decide +kernel)
lemma h30 : poly30.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 30 2) := by
  exact horner_step_g small_contains h31 fact30_check (m:=mul30) (by decide +kernel) (by decide +kernel)
lemma h29 : poly29.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 29 3) := by
  exact horner_step_g small_contains h30 fact29_check (m:=mul29) (by decide +kernel) (by decide +kernel)
lemma h28 : poly28.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 28 4) := by
  exact horner_step_g small_contains h29 fact28_check (m:=mul28) (by decide +kernel) (by decide +kernel)
lemma h27 : poly27.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 27 5) := by
  exact horner_step_g small_contains h28 fact27_check (m:=mul27) (by decide +kernel) (by decide +kernel)
lemma h26 : poly26.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 26 6) := by
  exact horner_step_g small_contains h27 fact26_check (m:=mul26) (by decide +kernel) (by decide +kernel)
lemma h25 : poly25.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 25 7) := by
  exact horner_step_g small_contains h26 fact25_check (m:=mul25) (by decide +kernel) (by decide +kernel)
lemma h24 : poly24.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 24 8) := by
  exact horner_step_g small_contains h25 fact24_check (m:=mul24) (by decide +kernel) (by decide +kernel)
lemma h23 : poly23.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 23 9) := by
  exact horner_step_g small_contains h24 fact23_check (m:=mul23) (by decide +kernel) (by decide +kernel)
lemma h22 : poly22.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 22 10) := by
  exact horner_step_g small_contains h23 fact22_check (m:=mul22) (by decide +kernel) (by decide +kernel)
lemma h21 : poly21.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 21 11) := by
  exact horner_step_g small_contains h22 fact21_check (m:=mul21) (by decide +kernel) (by decide +kernel)
lemma h20 : poly20.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 20 12) := by
  exact horner_step_g small_contains h21 fact20_check (m:=mul20) (by decide +kernel) (by decide +kernel)
lemma h19 : poly19.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 19 13) := by
  exact horner_step_g small_contains h20 fact19_check (m:=mul19) (by decide +kernel) (by decide +kernel)
lemma h18 : poly18.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 18 14) := by
  exact horner_step_g small_contains h19 fact18_check (m:=mul18) (by decide +kernel) (by decide +kernel)
lemma h17 : poly17.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 17 15) := by
  exact horner_step_g small_contains h18 fact17_check (m:=mul17) (by decide +kernel) (by decide +kernel)
lemma h16 : poly16.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 16 16) := by
  exact horner_step_g small_contains h17 fact16_check (m:=mul16) (by decide +kernel) (by decide +kernel)
lemma h15 : poly15.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 15 17) := by
  exact horner_step_g small_contains h16 fact15_check (m:=mul15) (by decide +kernel) (by decide +kernel)
lemma h14 : poly14.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 14 18) := by
  exact horner_step_g small_contains h15 fact14_check (m:=mul14) (by decide +kernel) (by decide +kernel)
lemma h13 : poly13.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 13 19) := by
  exact horner_step_g small_contains h14 fact13_check (m:=mul13) (by decide +kernel) (by decide +kernel)
lemma h12 : poly12.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 12 20) := by
  exact horner_step_g small_contains h13 fact12_check (m:=mul12) (by decide +kernel) (by decide +kernel)
lemma h11 : poly11.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 11 21) := by
  exact horner_step_g small_contains h12 fact11_check (m:=mul11) (by decide +kernel) (by decide +kernel)
lemma h10 : poly10.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 10 22) := by
  exact horner_step_g small_contains h11 fact10_check (m:=mul10) (by decide +kernel) (by decide +kernel)
lemma h9 : poly9.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 9 23) := by
  exact horner_step_g small_contains h10 fact9_check (m:=mul9) (by decide +kernel) (by decide +kernel)
lemma h8 : poly8.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 8 24) := by
  exact horner_step_g small_contains h9 fact8_check (m:=mul8) (by decide +kernel) (by decide +kernel)
lemma h7 : poly7.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 7 25) := by
  exact horner_step_g small_contains h8 fact7_check (m:=mul7) (by decide +kernel) (by decide +kernel)
lemma h6 : poly6.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 6 26) := by
  exact horner_step_g small_contains h7 fact6_check (m:=mul6) (by decide +kernel) (by decide +kernel)
lemma h5 : poly5.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 5 27) := by
  exact horner_step_g small_contains h6 fact5_check (m:=mul5) (by decide +kernel) (by decide +kernel)
lemma h4 : poly4.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 4 28) := by
  exact horner_step_g small_contains h5 fact4_check (m:=mul4) (by decide +kernel) (by decide +kernel)
lemma h3 : poly3.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 3 29) := by
  exact horner_step_g small_contains h4 fact3_check (m:=mul3) (by decide +kernel) (by decide +kernel)
lemma h2 : poly2.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 2 30) := by
  exact horner_step_g small_contains h3 fact2_check (m:=mul2) (by decide +kernel) (by decide +kernel)
lemma h1 : poly1.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 1 31) := by
  exact horner_step_g small_contains h2 fact1_check (m:=mul1) (by decide +kernel) (by decide +kernel)
lemma h0 : poly0.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 0 32) := by
  exact horner_step_g small_contains h1 fact0_check (m:=mul0) (by decide +kernel) (by decide +kernel)
lemma sq0_contains : sq0.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^0)) := by
  simpa using exp_from_horner_g small_contains (b:=poly0) (c:=sq0) (by decide +kernel) h0 (by decide +kernel)
lemma sq1_contains : sq1.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^1)) := by
  exact power_mul sq0_contains sq0_contains (by decide +kernel)
lemma sq2_contains : sq2.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^2)) := by
  exact power_mul sq1_contains sq1_contains (by decide +kernel)
lemma sq3_contains : sq3.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^3)) := by
  exact power_mul sq2_contains sq2_contains (by decide +kernel)
lemma sq4_contains : sq4.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^4)) := by
  exact power_mul sq3_contains sq3_contains (by decide +kernel)
lemma sq5_contains : sq5.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^5)) := by
  exact power_mul sq4_contains sq4_contains (by decide +kernel)
lemma sq6_contains : sq6.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^6)) := by
  exact power_mul sq5_contains sq5_contains (by decide +kernel)
lemma sq7_contains : sq7.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^7)) := by
  exact power_mul sq6_contains sq6_contains (by decide +kernel)
lemma sq8_contains : sq8.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^8)) := by
  exact power_mul sq7_contains sq7_contains (by decide +kernel)
lemma sq9_contains : sq9.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^9)) := by
  exact power_mul sq8_contains sq8_contains (by decide +kernel)
lemma sq10_contains : sq10.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^10)) := by
  exact power_mul sq9_contains sq9_contains (by decide +kernel)
lemma sq11_contains : sq11.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^11)) := by
  exact power_mul sq10_contains sq10_contains (by decide +kernel)
lemma phase_contains : sq11.Contains (rootPhase 1) := by
  have hh := sq11_contains
  rw [← Complex.exp_nat_mul] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold rootPhase
  congr 1
  norm_num
  ring
lemma root1_contains : root1.Contains (rootPhase 1) := phase_contains
lemma root2_contains : root2.Contains (rootPhase 2) := by
  have hh := CBox.mul_contains_g root1_contains root1_contains (c:=root2) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains_g mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains_g root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains_g root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid13_contains : mid13.Contains (rootPhase 12) := root12_contains
lemma root13_contains : root13.Contains (rootPhase 13) := by
  have hh := CBox.mul_contains_g mid13_contains root1_contains (c:=root13) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root26_contains : root26.Contains (rootPhase 26) := by
  have hh := CBox.mul_contains_g root13_contains root13_contains (c:=root26) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root52_contains : root52.Contains (rootPhase 52) := by
  have hh := CBox.mul_contains_g root26_contains root26_contains (c:=root52) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid53_contains : mid53.Contains (rootPhase 52) := root52_contains
lemma root53_contains : root53.Contains (rootPhase 53) := by
  have hh := CBox.mul_contains_g mid53_contains root1_contains (c:=root53) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root104_contains : root104.Contains (rootPhase 104) := by
  have hh := CBox.mul_contains_g root52_contains root52_contains (c:=root104) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid105_contains : mid105.Contains (rootPhase 104) := root104_contains
lemma root105_contains : root105.Contains (rootPhase 105) := by
  have hh := CBox.mul_contains_g mid105_contains root1_contains (c:=root105) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root106_contains : root106.Contains (rootPhase 106) := by
  have hh := CBox.mul_contains_g root53_contains root53_contains (c:=root106) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid107_contains : mid107.Contains (rootPhase 106) := root106_contains
lemma root107_contains : root107.Contains (rootPhase 107) := by
  have hh := CBox.mul_contains_g mid107_contains root1_contains (c:=root107) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root208_contains : root208.Contains (rootPhase 208) := by
  have hh := CBox.mul_contains_g root104_contains root104_contains (c:=root208) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid209_contains : mid209.Contains (rootPhase 208) := root208_contains
lemma root209_contains : root209.Contains (rootPhase 209) := by
  have hh := CBox.mul_contains_g mid209_contains root1_contains (c:=root209) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root210_contains : root210.Contains (rootPhase 210) := by
  have hh := CBox.mul_contains_g root105_contains root105_contains (c:=root210) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid211_contains : mid211.Contains (rootPhase 210) := root210_contains
lemma root211_contains : root211.Contains (rootPhase 211) := by
  have hh := CBox.mul_contains_g mid211_contains root1_contains (c:=root211) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root212_contains : root212.Contains (rootPhase 212) := by
  have hh := CBox.mul_contains_g root106_contains root106_contains (c:=root212) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid213_contains : mid213.Contains (rootPhase 212) := root212_contains
lemma root213_contains : root213.Contains (rootPhase 213) := by
  have hh := CBox.mul_contains_g mid213_contains root1_contains (c:=root213) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root214_contains : root214.Contains (rootPhase 214) := by
  have hh := CBox.mul_contains_g root107_contains root107_contains (c:=root214) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid215_contains : mid215.Contains (rootPhase 214) := root214_contains
lemma root215_contains : root215.Contains (rootPhase 215) := by
  have hh := CBox.mul_contains_g mid215_contains root1_contains (c:=root215) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root416_contains : root416.Contains (rootPhase 416) := by
  have hh := CBox.mul_contains_g root208_contains root208_contains (c:=root416) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid417_contains : mid417.Contains (rootPhase 416) := root416_contains
lemma root417_contains : root417.Contains (rootPhase 417) := by
  have hh := CBox.mul_contains_g mid417_contains root1_contains (c:=root417) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root418_contains : root418.Contains (rootPhase 418) := by
  have hh := CBox.mul_contains_g root209_contains root209_contains (c:=root418) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid419_contains : mid419.Contains (rootPhase 418) := root418_contains
lemma root419_contains : root419.Contains (rootPhase 419) := by
  have hh := CBox.mul_contains_g mid419_contains root1_contains (c:=root419) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root420_contains : root420.Contains (rootPhase 420) := by
  have hh := CBox.mul_contains_g root210_contains root210_contains (c:=root420) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid421_contains : mid421.Contains (rootPhase 420) := root420_contains
lemma root421_contains : root421.Contains (rootPhase 421) := by
  have hh := CBox.mul_contains_g mid421_contains root1_contains (c:=root421) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root422_contains : root422.Contains (rootPhase 422) := by
  have hh := CBox.mul_contains_g root211_contains root211_contains (c:=root422) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid423_contains : mid423.Contains (rootPhase 422) := root422_contains
lemma root423_contains : root423.Contains (rootPhase 423) := by
  have hh := CBox.mul_contains_g mid423_contains root1_contains (c:=root423) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root424_contains : root424.Contains (rootPhase 424) := by
  have hh := CBox.mul_contains_g root212_contains root212_contains (c:=root424) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid425_contains : mid425.Contains (rootPhase 424) := root424_contains
lemma root425_contains : root425.Contains (rootPhase 425) := by
  have hh := CBox.mul_contains_g mid425_contains root1_contains (c:=root425) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root426_contains : root426.Contains (rootPhase 426) := by
  have hh := CBox.mul_contains_g root213_contains root213_contains (c:=root426) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid427_contains : mid427.Contains (rootPhase 426) := root426_contains
lemma root427_contains : root427.Contains (rootPhase 427) := by
  have hh := CBox.mul_contains_g mid427_contains root1_contains (c:=root427) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root428_contains : root428.Contains (rootPhase 428) := by
  have hh := CBox.mul_contains_g root214_contains root214_contains (c:=root428) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid429_contains : mid429.Contains (rootPhase 428) := root428_contains
lemma root429_contains : root429.Contains (rootPhase 429) := by
  have hh := CBox.mul_contains_g mid429_contains root1_contains (c:=root429) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root430_contains : root430.Contains (rootPhase 430) := by
  have hh := CBox.mul_contains_g root215_contains root215_contains (c:=root430) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid431_contains : mid431.Contains (rootPhase 430) := root430_contains
lemma root431_contains : root431.Contains (rootPhase 431) := by
  have hh := CBox.mul_contains_g mid431_contains root1_contains (c:=root431) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root832_contains : root832.Contains (rootPhase 832) := by
  have hh := CBox.mul_contains_g root416_contains root416_contains (c:=root832) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid833_contains : mid833.Contains (rootPhase 832) := root832_contains
lemma root833_contains : root833.Contains (rootPhase 833) := by
  have hh := CBox.mul_contains_g mid833_contains root1_contains (c:=root833) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root834_contains : root834.Contains (rootPhase 834) := by
  have hh := CBox.mul_contains_g root417_contains root417_contains (c:=root834) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid835_contains : mid835.Contains (rootPhase 834) := root834_contains
lemma root835_contains : root835.Contains (rootPhase 835) := by
  have hh := CBox.mul_contains_g mid835_contains root1_contains (c:=root835) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root836_contains : root836.Contains (rootPhase 836) := by
  have hh := CBox.mul_contains_g root418_contains root418_contains (c:=root836) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid837_contains : mid837.Contains (rootPhase 836) := root836_contains
lemma root837_contains : root837.Contains (rootPhase 837) := by
  have hh := CBox.mul_contains_g mid837_contains root1_contains (c:=root837) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root838_contains : root838.Contains (rootPhase 838) := by
  have hh := CBox.mul_contains_g root419_contains root419_contains (c:=root838) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid839_contains : mid839.Contains (rootPhase 838) := root838_contains
lemma root839_contains : root839.Contains (rootPhase 839) := by
  have hh := CBox.mul_contains_g mid839_contains root1_contains (c:=root839) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root840_contains : root840.Contains (rootPhase 840) := by
  have hh := CBox.mul_contains_g root420_contains root420_contains (c:=root840) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid841_contains : mid841.Contains (rootPhase 840) := root840_contains
lemma root841_contains : root841.Contains (rootPhase 841) := by
  have hh := CBox.mul_contains_g mid841_contains root1_contains (c:=root841) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root842_contains : root842.Contains (rootPhase 842) := by
  have hh := CBox.mul_contains_g root421_contains root421_contains (c:=root842) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid843_contains : mid843.Contains (rootPhase 842) := root842_contains
lemma root843_contains : root843.Contains (rootPhase 843) := by
  have hh := CBox.mul_contains_g mid843_contains root1_contains (c:=root843) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root844_contains : root844.Contains (rootPhase 844) := by
  have hh := CBox.mul_contains_g root422_contains root422_contains (c:=root844) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid845_contains : mid845.Contains (rootPhase 844) := root844_contains
lemma root845_contains : root845.Contains (rootPhase 845) := by
  have hh := CBox.mul_contains_g mid845_contains root1_contains (c:=root845) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root846_contains : root846.Contains (rootPhase 846) := by
  have hh := CBox.mul_contains_g root423_contains root423_contains (c:=root846) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid847_contains : mid847.Contains (rootPhase 846) := root846_contains
lemma root847_contains : root847.Contains (rootPhase 847) := by
  have hh := CBox.mul_contains_g mid847_contains root1_contains (c:=root847) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root848_contains : root848.Contains (rootPhase 848) := by
  have hh := CBox.mul_contains_g root424_contains root424_contains (c:=root848) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid849_contains : mid849.Contains (rootPhase 848) := root848_contains
lemma root849_contains : root849.Contains (rootPhase 849) := by
  have hh := CBox.mul_contains_g mid849_contains root1_contains (c:=root849) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root850_contains : root850.Contains (rootPhase 850) := by
  have hh := CBox.mul_contains_g root425_contains root425_contains (c:=root850) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid851_contains : mid851.Contains (rootPhase 850) := root850_contains
lemma root851_contains : root851.Contains (rootPhase 851) := by
  have hh := CBox.mul_contains_g mid851_contains root1_contains (c:=root851) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root852_contains : root852.Contains (rootPhase 852) := by
  have hh := CBox.mul_contains_g root426_contains root426_contains (c:=root852) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid853_contains : mid853.Contains (rootPhase 852) := root852_contains
lemma root853_contains : root853.Contains (rootPhase 853) := by
  have hh := CBox.mul_contains_g mid853_contains root1_contains (c:=root853) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root854_contains : root854.Contains (rootPhase 854) := by
  have hh := CBox.mul_contains_g root427_contains root427_contains (c:=root854) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid855_contains : mid855.Contains (rootPhase 854) := root854_contains
lemma root855_contains : root855.Contains (rootPhase 855) := by
  have hh := CBox.mul_contains_g mid855_contains root1_contains (c:=root855) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root856_contains : root856.Contains (rootPhase 856) := by
  have hh := CBox.mul_contains_g root428_contains root428_contains (c:=root856) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid857_contains : mid857.Contains (rootPhase 856) := root856_contains
lemma root857_contains : root857.Contains (rootPhase 857) := by
  have hh := CBox.mul_contains_g mid857_contains root1_contains (c:=root857) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root858_contains : root858.Contains (rootPhase 858) := by
  have hh := CBox.mul_contains_g root429_contains root429_contains (c:=root858) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid859_contains : mid859.Contains (rootPhase 858) := root858_contains
lemma root859_contains : root859.Contains (rootPhase 859) := by
  have hh := CBox.mul_contains_g mid859_contains root1_contains (c:=root859) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root860_contains : root860.Contains (rootPhase 860) := by
  have hh := CBox.mul_contains_g root430_contains root430_contains (c:=root860) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid861_contains : mid861.Contains (rootPhase 860) := root860_contains
lemma root861_contains : root861.Contains (rootPhase 861) := by
  have hh := CBox.mul_contains_g mid861_contains root1_contains (c:=root861) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root862_contains : root862.Contains (rootPhase 862) := by
  have hh := CBox.mul_contains_g root431_contains root431_contains (c:=root862) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid863_contains : mid863.Contains (rootPhase 862) := root862_contains
lemma root863_contains : root863.Contains (rootPhase 863) := by
  have hh := CBox.mul_contains_g mid863_contains root1_contains (c:=root863) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
end IntegerRoots
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
lemma roots26_contains_g_oai (j : Fin 32) : (roots26 j).Contains (rootPhase (832+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root832_contains
  · exact IntegerRoots.root833_contains
  · exact IntegerRoots.root834_contains
  · exact IntegerRoots.root835_contains
  · exact IntegerRoots.root836_contains
  · exact IntegerRoots.root837_contains
  · exact IntegerRoots.root838_contains
  · exact IntegerRoots.root839_contains
  · exact IntegerRoots.root840_contains
  · exact IntegerRoots.root841_contains
  · exact IntegerRoots.root842_contains
  · exact IntegerRoots.root843_contains
  · exact IntegerRoots.root844_contains
  · exact IntegerRoots.root845_contains
  · exact IntegerRoots.root846_contains
  · exact IntegerRoots.root847_contains
  · exact IntegerRoots.root848_contains
  · exact IntegerRoots.root849_contains
  · exact IntegerRoots.root850_contains
  · exact IntegerRoots.root851_contains
  · exact IntegerRoots.root852_contains
  · exact IntegerRoots.root853_contains
  · exact IntegerRoots.root854_contains
  · exact IntegerRoots.root855_contains
  · exact IntegerRoots.root856_contains
  · exact IntegerRoots.root857_contains
  · exact IntegerRoots.root858_contains
  · exact IntegerRoots.root859_contains
  · exact IntegerRoots.root860_contains
  · exact IntegerRoots.root861_contains
  · exact IntegerRoots.root862_contains
  · exact IntegerRoots.root863_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots26_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots26_contains_g_oai
