-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:07:43.386196+00:00
-- url     : https://prove2.me/submissions/8387e7b6-141d-4c71-bdd4-0197b9002c72

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G059
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G094
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
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains_g root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains_g root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid9_contains : mid9.Contains (rootPhase 8) := root8_contains
lemma root9_contains : root9.Contains (rootPhase 9) := by
  have hh := CBox.mul_contains_g mid9_contains root1_contains (c:=root9) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root18_contains : root18.Contains (rootPhase 18) := by
  have hh := CBox.mul_contains_g root9_contains root9_contains (c:=root18) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid19_contains : mid19.Contains (rootPhase 18) := root18_contains
lemma root19_contains : root19.Contains (rootPhase 19) := by
  have hh := CBox.mul_contains_g mid19_contains root1_contains (c:=root19) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains_g root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains_g mid37_contains root1_contains (c:=root37) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root38_contains : root38.Contains (rootPhase 38) := by
  have hh := CBox.mul_contains_g root19_contains root19_contains (c:=root38) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid39_contains : mid39.Contains (rootPhase 38) := root38_contains
lemma root39_contains : root39.Contains (rootPhase 39) := by
  have hh := CBox.mul_contains_g mid39_contains root1_contains (c:=root39) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root72_contains : root72.Contains (rootPhase 72) := by
  have hh := CBox.mul_contains_g root36_contains root36_contains (c:=root72) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid73_contains : mid73.Contains (rootPhase 72) := root72_contains
lemma root73_contains : root73.Contains (rootPhase 73) := by
  have hh := CBox.mul_contains_g mid73_contains root1_contains (c:=root73) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root74_contains : root74.Contains (rootPhase 74) := by
  have hh := CBox.mul_contains_g root37_contains root37_contains (c:=root74) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid75_contains : mid75.Contains (rootPhase 74) := root74_contains
lemma root75_contains : root75.Contains (rootPhase 75) := by
  have hh := CBox.mul_contains_g mid75_contains root1_contains (c:=root75) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root76_contains : root76.Contains (rootPhase 76) := by
  have hh := CBox.mul_contains_g root38_contains root38_contains (c:=root76) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid77_contains : mid77.Contains (rootPhase 76) := root76_contains
lemma root77_contains : root77.Contains (rootPhase 77) := by
  have hh := CBox.mul_contains_g mid77_contains root1_contains (c:=root77) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root78_contains : root78.Contains (rootPhase 78) := by
  have hh := CBox.mul_contains_g root39_contains root39_contains (c:=root78) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid79_contains : mid79.Contains (rootPhase 78) := root78_contains
lemma root79_contains : root79.Contains (rootPhase 79) := by
  have hh := CBox.mul_contains_g mid79_contains root1_contains (c:=root79) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root144_contains : root144.Contains (rootPhase 144) := by
  have hh := CBox.mul_contains_g root72_contains root72_contains (c:=root144) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid145_contains : mid145.Contains (rootPhase 144) := root144_contains
lemma root145_contains : root145.Contains (rootPhase 145) := by
  have hh := CBox.mul_contains_g mid145_contains root1_contains (c:=root145) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root146_contains : root146.Contains (rootPhase 146) := by
  have hh := CBox.mul_contains_g root73_contains root73_contains (c:=root146) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid147_contains : mid147.Contains (rootPhase 146) := root146_contains
lemma root147_contains : root147.Contains (rootPhase 147) := by
  have hh := CBox.mul_contains_g mid147_contains root1_contains (c:=root147) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root148_contains : root148.Contains (rootPhase 148) := by
  have hh := CBox.mul_contains_g root74_contains root74_contains (c:=root148) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid149_contains : mid149.Contains (rootPhase 148) := root148_contains
lemma root149_contains : root149.Contains (rootPhase 149) := by
  have hh := CBox.mul_contains_g mid149_contains root1_contains (c:=root149) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root150_contains : root150.Contains (rootPhase 150) := by
  have hh := CBox.mul_contains_g root75_contains root75_contains (c:=root150) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid151_contains : mid151.Contains (rootPhase 150) := root150_contains
lemma root151_contains : root151.Contains (rootPhase 151) := by
  have hh := CBox.mul_contains_g mid151_contains root1_contains (c:=root151) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root152_contains : root152.Contains (rootPhase 152) := by
  have hh := CBox.mul_contains_g root76_contains root76_contains (c:=root152) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid153_contains : mid153.Contains (rootPhase 152) := root152_contains
lemma root153_contains : root153.Contains (rootPhase 153) := by
  have hh := CBox.mul_contains_g mid153_contains root1_contains (c:=root153) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root154_contains : root154.Contains (rootPhase 154) := by
  have hh := CBox.mul_contains_g root77_contains root77_contains (c:=root154) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid155_contains : mid155.Contains (rootPhase 154) := root154_contains
lemma root155_contains : root155.Contains (rootPhase 155) := by
  have hh := CBox.mul_contains_g mid155_contains root1_contains (c:=root155) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root156_contains : root156.Contains (rootPhase 156) := by
  have hh := CBox.mul_contains_g root78_contains root78_contains (c:=root156) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid157_contains : mid157.Contains (rootPhase 156) := root156_contains
lemma root157_contains : root157.Contains (rootPhase 157) := by
  have hh := CBox.mul_contains_g mid157_contains root1_contains (c:=root157) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root158_contains : root158.Contains (rootPhase 158) := by
  have hh := CBox.mul_contains_g root79_contains root79_contains (c:=root158) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid159_contains : mid159.Contains (rootPhase 158) := root158_contains
lemma root159_contains : root159.Contains (rootPhase 159) := by
  have hh := CBox.mul_contains_g mid159_contains root1_contains (c:=root159) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root288_contains : root288.Contains (rootPhase 288) := by
  have hh := CBox.mul_contains_g root144_contains root144_contains (c:=root288) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid289_contains : mid289.Contains (rootPhase 288) := root288_contains
lemma root289_contains : root289.Contains (rootPhase 289) := by
  have hh := CBox.mul_contains_g mid289_contains root1_contains (c:=root289) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root290_contains : root290.Contains (rootPhase 290) := by
  have hh := CBox.mul_contains_g root145_contains root145_contains (c:=root290) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid291_contains : mid291.Contains (rootPhase 290) := root290_contains
lemma root291_contains : root291.Contains (rootPhase 291) := by
  have hh := CBox.mul_contains_g mid291_contains root1_contains (c:=root291) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root292_contains : root292.Contains (rootPhase 292) := by
  have hh := CBox.mul_contains_g root146_contains root146_contains (c:=root292) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid293_contains : mid293.Contains (rootPhase 292) := root292_contains
lemma root293_contains : root293.Contains (rootPhase 293) := by
  have hh := CBox.mul_contains_g mid293_contains root1_contains (c:=root293) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root294_contains : root294.Contains (rootPhase 294) := by
  have hh := CBox.mul_contains_g root147_contains root147_contains (c:=root294) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid295_contains : mid295.Contains (rootPhase 294) := root294_contains
lemma root295_contains : root295.Contains (rootPhase 295) := by
  have hh := CBox.mul_contains_g mid295_contains root1_contains (c:=root295) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root296_contains : root296.Contains (rootPhase 296) := by
  have hh := CBox.mul_contains_g root148_contains root148_contains (c:=root296) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid297_contains : mid297.Contains (rootPhase 296) := root296_contains
lemma root297_contains : root297.Contains (rootPhase 297) := by
  have hh := CBox.mul_contains_g mid297_contains root1_contains (c:=root297) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root298_contains : root298.Contains (rootPhase 298) := by
  have hh := CBox.mul_contains_g root149_contains root149_contains (c:=root298) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid299_contains : mid299.Contains (rootPhase 298) := root298_contains
lemma root299_contains : root299.Contains (rootPhase 299) := by
  have hh := CBox.mul_contains_g mid299_contains root1_contains (c:=root299) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root300_contains : root300.Contains (rootPhase 300) := by
  have hh := CBox.mul_contains_g root150_contains root150_contains (c:=root300) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid301_contains : mid301.Contains (rootPhase 300) := root300_contains
lemma root301_contains : root301.Contains (rootPhase 301) := by
  have hh := CBox.mul_contains_g mid301_contains root1_contains (c:=root301) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root302_contains : root302.Contains (rootPhase 302) := by
  have hh := CBox.mul_contains_g root151_contains root151_contains (c:=root302) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid303_contains : mid303.Contains (rootPhase 302) := root302_contains
lemma root303_contains : root303.Contains (rootPhase 303) := by
  have hh := CBox.mul_contains_g mid303_contains root1_contains (c:=root303) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root304_contains : root304.Contains (rootPhase 304) := by
  have hh := CBox.mul_contains_g root152_contains root152_contains (c:=root304) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid305_contains : mid305.Contains (rootPhase 304) := root304_contains
lemma root305_contains : root305.Contains (rootPhase 305) := by
  have hh := CBox.mul_contains_g mid305_contains root1_contains (c:=root305) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root306_contains : root306.Contains (rootPhase 306) := by
  have hh := CBox.mul_contains_g root153_contains root153_contains (c:=root306) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid307_contains : mid307.Contains (rootPhase 306) := root306_contains
lemma root307_contains : root307.Contains (rootPhase 307) := by
  have hh := CBox.mul_contains_g mid307_contains root1_contains (c:=root307) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root308_contains : root308.Contains (rootPhase 308) := by
  have hh := CBox.mul_contains_g root154_contains root154_contains (c:=root308) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid309_contains : mid309.Contains (rootPhase 308) := root308_contains
lemma root309_contains : root309.Contains (rootPhase 309) := by
  have hh := CBox.mul_contains_g mid309_contains root1_contains (c:=root309) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root310_contains : root310.Contains (rootPhase 310) := by
  have hh := CBox.mul_contains_g root155_contains root155_contains (c:=root310) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid311_contains : mid311.Contains (rootPhase 310) := root310_contains
lemma root311_contains : root311.Contains (rootPhase 311) := by
  have hh := CBox.mul_contains_g mid311_contains root1_contains (c:=root311) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root312_contains : root312.Contains (rootPhase 312) := by
  have hh := CBox.mul_contains_g root156_contains root156_contains (c:=root312) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid313_contains : mid313.Contains (rootPhase 312) := root312_contains
lemma root313_contains : root313.Contains (rootPhase 313) := by
  have hh := CBox.mul_contains_g mid313_contains root1_contains (c:=root313) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root314_contains : root314.Contains (rootPhase 314) := by
  have hh := CBox.mul_contains_g root157_contains root157_contains (c:=root314) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid315_contains : mid315.Contains (rootPhase 314) := root314_contains
lemma root315_contains : root315.Contains (rootPhase 315) := by
  have hh := CBox.mul_contains_g mid315_contains root1_contains (c:=root315) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root316_contains : root316.Contains (rootPhase 316) := by
  have hh := CBox.mul_contains_g root158_contains root158_contains (c:=root316) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid317_contains : mid317.Contains (rootPhase 316) := root316_contains
lemma root317_contains : root317.Contains (rootPhase 317) := by
  have hh := CBox.mul_contains_g mid317_contains root1_contains (c:=root317) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root318_contains : root318.Contains (rootPhase 318) := by
  have hh := CBox.mul_contains_g root159_contains root159_contains (c:=root318) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid319_contains : mid319.Contains (rootPhase 318) := root318_contains
lemma root319_contains : root319.Contains (rootPhase 319) := by
  have hh := CBox.mul_contains_g mid319_contains root1_contains (c:=root319) (by decide +kernel)
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
lemma roots9_contains_g_oai (j : Fin 32) : (roots9 j).Contains (rootPhase (288+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root288_contains
  · exact IntegerRoots.root289_contains
  · exact IntegerRoots.root290_contains
  · exact IntegerRoots.root291_contains
  · exact IntegerRoots.root292_contains
  · exact IntegerRoots.root293_contains
  · exact IntegerRoots.root294_contains
  · exact IntegerRoots.root295_contains
  · exact IntegerRoots.root296_contains
  · exact IntegerRoots.root297_contains
  · exact IntegerRoots.root298_contains
  · exact IntegerRoots.root299_contains
  · exact IntegerRoots.root300_contains
  · exact IntegerRoots.root301_contains
  · exact IntegerRoots.root302_contains
  · exact IntegerRoots.root303_contains
  · exact IntegerRoots.root304_contains
  · exact IntegerRoots.root305_contains
  · exact IntegerRoots.root306_contains
  · exact IntegerRoots.root307_contains
  · exact IntegerRoots.root308_contains
  · exact IntegerRoots.root309_contains
  · exact IntegerRoots.root310_contains
  · exact IntegerRoots.root311_contains
  · exact IntegerRoots.root312_contains
  · exact IntegerRoots.root313_contains
  · exact IntegerRoots.root314_contains
  · exact IntegerRoots.root315_contains
  · exact IntegerRoots.root316_contains
  · exact IntegerRoots.root317_contains
  · exact IntegerRoots.root318_contains
  · exact IntegerRoots.root319_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots9_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots9_contains_g_oai
