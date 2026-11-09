-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots27_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:43.981793+00:00
-- url     : https://prove2.me/submissions/c393a46c-0732-4809-8686-4e171f147b3f

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
lemma mid27_contains : mid27.Contains (rootPhase 26) := root26_contains
lemma root27_contains : root27.Contains (rootPhase 27) := by
  have hh := CBox.mul_contains_g mid27_contains root1_contains (c:=root27) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root54_contains : root54.Contains (rootPhase 54) := by
  have hh := CBox.mul_contains_g root27_contains root27_contains (c:=root54) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid55_contains : mid55.Contains (rootPhase 54) := root54_contains
lemma root55_contains : root55.Contains (rootPhase 55) := by
  have hh := CBox.mul_contains_g mid55_contains root1_contains (c:=root55) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root108_contains : root108.Contains (rootPhase 108) := by
  have hh := CBox.mul_contains_g root54_contains root54_contains (c:=root108) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid109_contains : mid109.Contains (rootPhase 108) := root108_contains
lemma root109_contains : root109.Contains (rootPhase 109) := by
  have hh := CBox.mul_contains_g mid109_contains root1_contains (c:=root109) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root110_contains : root110.Contains (rootPhase 110) := by
  have hh := CBox.mul_contains_g root55_contains root55_contains (c:=root110) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid111_contains : mid111.Contains (rootPhase 110) := root110_contains
lemma root111_contains : root111.Contains (rootPhase 111) := by
  have hh := CBox.mul_contains_g mid111_contains root1_contains (c:=root111) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root216_contains : root216.Contains (rootPhase 216) := by
  have hh := CBox.mul_contains_g root108_contains root108_contains (c:=root216) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid217_contains : mid217.Contains (rootPhase 216) := root216_contains
lemma root217_contains : root217.Contains (rootPhase 217) := by
  have hh := CBox.mul_contains_g mid217_contains root1_contains (c:=root217) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root218_contains : root218.Contains (rootPhase 218) := by
  have hh := CBox.mul_contains_g root109_contains root109_contains (c:=root218) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid219_contains : mid219.Contains (rootPhase 218) := root218_contains
lemma root219_contains : root219.Contains (rootPhase 219) := by
  have hh := CBox.mul_contains_g mid219_contains root1_contains (c:=root219) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root220_contains : root220.Contains (rootPhase 220) := by
  have hh := CBox.mul_contains_g root110_contains root110_contains (c:=root220) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid221_contains : mid221.Contains (rootPhase 220) := root220_contains
lemma root221_contains : root221.Contains (rootPhase 221) := by
  have hh := CBox.mul_contains_g mid221_contains root1_contains (c:=root221) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root222_contains : root222.Contains (rootPhase 222) := by
  have hh := CBox.mul_contains_g root111_contains root111_contains (c:=root222) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid223_contains : mid223.Contains (rootPhase 222) := root222_contains
lemma root223_contains : root223.Contains (rootPhase 223) := by
  have hh := CBox.mul_contains_g mid223_contains root1_contains (c:=root223) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root432_contains : root432.Contains (rootPhase 432) := by
  have hh := CBox.mul_contains_g root216_contains root216_contains (c:=root432) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid433_contains : mid433.Contains (rootPhase 432) := root432_contains
lemma root433_contains : root433.Contains (rootPhase 433) := by
  have hh := CBox.mul_contains_g mid433_contains root1_contains (c:=root433) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root434_contains : root434.Contains (rootPhase 434) := by
  have hh := CBox.mul_contains_g root217_contains root217_contains (c:=root434) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid435_contains : mid435.Contains (rootPhase 434) := root434_contains
lemma root435_contains : root435.Contains (rootPhase 435) := by
  have hh := CBox.mul_contains_g mid435_contains root1_contains (c:=root435) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root436_contains : root436.Contains (rootPhase 436) := by
  have hh := CBox.mul_contains_g root218_contains root218_contains (c:=root436) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid437_contains : mid437.Contains (rootPhase 436) := root436_contains
lemma root437_contains : root437.Contains (rootPhase 437) := by
  have hh := CBox.mul_contains_g mid437_contains root1_contains (c:=root437) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root438_contains : root438.Contains (rootPhase 438) := by
  have hh := CBox.mul_contains_g root219_contains root219_contains (c:=root438) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid439_contains : mid439.Contains (rootPhase 438) := root438_contains
lemma root439_contains : root439.Contains (rootPhase 439) := by
  have hh := CBox.mul_contains_g mid439_contains root1_contains (c:=root439) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root440_contains : root440.Contains (rootPhase 440) := by
  have hh := CBox.mul_contains_g root220_contains root220_contains (c:=root440) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid441_contains : mid441.Contains (rootPhase 440) := root440_contains
lemma root441_contains : root441.Contains (rootPhase 441) := by
  have hh := CBox.mul_contains_g mid441_contains root1_contains (c:=root441) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root442_contains : root442.Contains (rootPhase 442) := by
  have hh := CBox.mul_contains_g root221_contains root221_contains (c:=root442) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid443_contains : mid443.Contains (rootPhase 442) := root442_contains
lemma root443_contains : root443.Contains (rootPhase 443) := by
  have hh := CBox.mul_contains_g mid443_contains root1_contains (c:=root443) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root444_contains : root444.Contains (rootPhase 444) := by
  have hh := CBox.mul_contains_g root222_contains root222_contains (c:=root444) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid445_contains : mid445.Contains (rootPhase 444) := root444_contains
lemma root445_contains : root445.Contains (rootPhase 445) := by
  have hh := CBox.mul_contains_g mid445_contains root1_contains (c:=root445) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root446_contains : root446.Contains (rootPhase 446) := by
  have hh := CBox.mul_contains_g root223_contains root223_contains (c:=root446) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid447_contains : mid447.Contains (rootPhase 446) := root446_contains
lemma root447_contains : root447.Contains (rootPhase 447) := by
  have hh := CBox.mul_contains_g mid447_contains root1_contains (c:=root447) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root864_contains : root864.Contains (rootPhase 864) := by
  have hh := CBox.mul_contains_g root432_contains root432_contains (c:=root864) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid865_contains : mid865.Contains (rootPhase 864) := root864_contains
lemma root865_contains : root865.Contains (rootPhase 865) := by
  have hh := CBox.mul_contains_g mid865_contains root1_contains (c:=root865) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root866_contains : root866.Contains (rootPhase 866) := by
  have hh := CBox.mul_contains_g root433_contains root433_contains (c:=root866) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid867_contains : mid867.Contains (rootPhase 866) := root866_contains
lemma root867_contains : root867.Contains (rootPhase 867) := by
  have hh := CBox.mul_contains_g mid867_contains root1_contains (c:=root867) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root868_contains : root868.Contains (rootPhase 868) := by
  have hh := CBox.mul_contains_g root434_contains root434_contains (c:=root868) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid869_contains : mid869.Contains (rootPhase 868) := root868_contains
lemma root869_contains : root869.Contains (rootPhase 869) := by
  have hh := CBox.mul_contains_g mid869_contains root1_contains (c:=root869) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root870_contains : root870.Contains (rootPhase 870) := by
  have hh := CBox.mul_contains_g root435_contains root435_contains (c:=root870) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid871_contains : mid871.Contains (rootPhase 870) := root870_contains
lemma root871_contains : root871.Contains (rootPhase 871) := by
  have hh := CBox.mul_contains_g mid871_contains root1_contains (c:=root871) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root872_contains : root872.Contains (rootPhase 872) := by
  have hh := CBox.mul_contains_g root436_contains root436_contains (c:=root872) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid873_contains : mid873.Contains (rootPhase 872) := root872_contains
lemma root873_contains : root873.Contains (rootPhase 873) := by
  have hh := CBox.mul_contains_g mid873_contains root1_contains (c:=root873) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root874_contains : root874.Contains (rootPhase 874) := by
  have hh := CBox.mul_contains_g root437_contains root437_contains (c:=root874) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid875_contains : mid875.Contains (rootPhase 874) := root874_contains
lemma root875_contains : root875.Contains (rootPhase 875) := by
  have hh := CBox.mul_contains_g mid875_contains root1_contains (c:=root875) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root876_contains : root876.Contains (rootPhase 876) := by
  have hh := CBox.mul_contains_g root438_contains root438_contains (c:=root876) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid877_contains : mid877.Contains (rootPhase 876) := root876_contains
lemma root877_contains : root877.Contains (rootPhase 877) := by
  have hh := CBox.mul_contains_g mid877_contains root1_contains (c:=root877) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root878_contains : root878.Contains (rootPhase 878) := by
  have hh := CBox.mul_contains_g root439_contains root439_contains (c:=root878) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid879_contains : mid879.Contains (rootPhase 878) := root878_contains
lemma root879_contains : root879.Contains (rootPhase 879) := by
  have hh := CBox.mul_contains_g mid879_contains root1_contains (c:=root879) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root880_contains : root880.Contains (rootPhase 880) := by
  have hh := CBox.mul_contains_g root440_contains root440_contains (c:=root880) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid881_contains : mid881.Contains (rootPhase 880) := root880_contains
lemma root881_contains : root881.Contains (rootPhase 881) := by
  have hh := CBox.mul_contains_g mid881_contains root1_contains (c:=root881) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root882_contains : root882.Contains (rootPhase 882) := by
  have hh := CBox.mul_contains_g root441_contains root441_contains (c:=root882) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid883_contains : mid883.Contains (rootPhase 882) := root882_contains
lemma root883_contains : root883.Contains (rootPhase 883) := by
  have hh := CBox.mul_contains_g mid883_contains root1_contains (c:=root883) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root884_contains : root884.Contains (rootPhase 884) := by
  have hh := CBox.mul_contains_g root442_contains root442_contains (c:=root884) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid885_contains : mid885.Contains (rootPhase 884) := root884_contains
lemma root885_contains : root885.Contains (rootPhase 885) := by
  have hh := CBox.mul_contains_g mid885_contains root1_contains (c:=root885) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root886_contains : root886.Contains (rootPhase 886) := by
  have hh := CBox.mul_contains_g root443_contains root443_contains (c:=root886) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid887_contains : mid887.Contains (rootPhase 886) := root886_contains
lemma root887_contains : root887.Contains (rootPhase 887) := by
  have hh := CBox.mul_contains_g mid887_contains root1_contains (c:=root887) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root888_contains : root888.Contains (rootPhase 888) := by
  have hh := CBox.mul_contains_g root444_contains root444_contains (c:=root888) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid889_contains : mid889.Contains (rootPhase 888) := root888_contains
lemma root889_contains : root889.Contains (rootPhase 889) := by
  have hh := CBox.mul_contains_g mid889_contains root1_contains (c:=root889) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root890_contains : root890.Contains (rootPhase 890) := by
  have hh := CBox.mul_contains_g root445_contains root445_contains (c:=root890) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid891_contains : mid891.Contains (rootPhase 890) := root890_contains
lemma root891_contains : root891.Contains (rootPhase 891) := by
  have hh := CBox.mul_contains_g mid891_contains root1_contains (c:=root891) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root892_contains : root892.Contains (rootPhase 892) := by
  have hh := CBox.mul_contains_g root446_contains root446_contains (c:=root892) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid893_contains : mid893.Contains (rootPhase 892) := root892_contains
lemma root893_contains : root893.Contains (rootPhase 893) := by
  have hh := CBox.mul_contains_g mid893_contains root1_contains (c:=root893) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root894_contains : root894.Contains (rootPhase 894) := by
  have hh := CBox.mul_contains_g root447_contains root447_contains (c:=root894) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid895_contains : mid895.Contains (rootPhase 894) := root894_contains
lemma root895_contains : root895.Contains (rootPhase 895) := by
  have hh := CBox.mul_contains_g mid895_contains root1_contains (c:=root895) (by decide +kernel)
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
lemma roots27_contains_g_oai (j : Fin 32) : (roots27 j).Contains (rootPhase (864+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root864_contains
  · exact IntegerRoots.root865_contains
  · exact IntegerRoots.root866_contains
  · exact IntegerRoots.root867_contains
  · exact IntegerRoots.root868_contains
  · exact IntegerRoots.root869_contains
  · exact IntegerRoots.root870_contains
  · exact IntegerRoots.root871_contains
  · exact IntegerRoots.root872_contains
  · exact IntegerRoots.root873_contains
  · exact IntegerRoots.root874_contains
  · exact IntegerRoots.root875_contains
  · exact IntegerRoots.root876_contains
  · exact IntegerRoots.root877_contains
  · exact IntegerRoots.root878_contains
  · exact IntegerRoots.root879_contains
  · exact IntegerRoots.root880_contains
  · exact IntegerRoots.root881_contains
  · exact IntegerRoots.root882_contains
  · exact IntegerRoots.root883_contains
  · exact IntegerRoots.root884_contains
  · exact IntegerRoots.root885_contains
  · exact IntegerRoots.root886_contains
  · exact IntegerRoots.root887_contains
  · exact IntegerRoots.root888_contains
  · exact IntegerRoots.root889_contains
  · exact IntegerRoots.root890_contains
  · exact IntegerRoots.root891_contains
  · exact IntegerRoots.root892_contains
  · exact IntegerRoots.root893_contains
  · exact IntegerRoots.root894_contains
  · exact IntegerRoots.root895_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots27_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots27_contains_g_oai
