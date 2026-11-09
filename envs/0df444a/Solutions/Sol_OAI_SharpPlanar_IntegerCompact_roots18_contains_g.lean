-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots18_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:30:08.112142+00:00
-- url     : https://prove2.me/submissions/1d172992-aab6-4792-8ca4-d3a59b90ffc0

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
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains_g root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains_g mid37_contains root1_contains (c:=root37) (by decide +kernel)
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
lemma root576_contains : root576.Contains (rootPhase 576) := by
  have hh := CBox.mul_contains_g root288_contains root288_contains (c:=root576) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid577_contains : mid577.Contains (rootPhase 576) := root576_contains
lemma root577_contains : root577.Contains (rootPhase 577) := by
  have hh := CBox.mul_contains_g mid577_contains root1_contains (c:=root577) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root578_contains : root578.Contains (rootPhase 578) := by
  have hh := CBox.mul_contains_g root289_contains root289_contains (c:=root578) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid579_contains : mid579.Contains (rootPhase 578) := root578_contains
lemma root579_contains : root579.Contains (rootPhase 579) := by
  have hh := CBox.mul_contains_g mid579_contains root1_contains (c:=root579) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root580_contains : root580.Contains (rootPhase 580) := by
  have hh := CBox.mul_contains_g root290_contains root290_contains (c:=root580) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid581_contains : mid581.Contains (rootPhase 580) := root580_contains
lemma root581_contains : root581.Contains (rootPhase 581) := by
  have hh := CBox.mul_contains_g mid581_contains root1_contains (c:=root581) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root582_contains : root582.Contains (rootPhase 582) := by
  have hh := CBox.mul_contains_g root291_contains root291_contains (c:=root582) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid583_contains : mid583.Contains (rootPhase 582) := root582_contains
lemma root583_contains : root583.Contains (rootPhase 583) := by
  have hh := CBox.mul_contains_g mid583_contains root1_contains (c:=root583) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root584_contains : root584.Contains (rootPhase 584) := by
  have hh := CBox.mul_contains_g root292_contains root292_contains (c:=root584) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid585_contains : mid585.Contains (rootPhase 584) := root584_contains
lemma root585_contains : root585.Contains (rootPhase 585) := by
  have hh := CBox.mul_contains_g mid585_contains root1_contains (c:=root585) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root586_contains : root586.Contains (rootPhase 586) := by
  have hh := CBox.mul_contains_g root293_contains root293_contains (c:=root586) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid587_contains : mid587.Contains (rootPhase 586) := root586_contains
lemma root587_contains : root587.Contains (rootPhase 587) := by
  have hh := CBox.mul_contains_g mid587_contains root1_contains (c:=root587) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root588_contains : root588.Contains (rootPhase 588) := by
  have hh := CBox.mul_contains_g root294_contains root294_contains (c:=root588) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid589_contains : mid589.Contains (rootPhase 588) := root588_contains
lemma root589_contains : root589.Contains (rootPhase 589) := by
  have hh := CBox.mul_contains_g mid589_contains root1_contains (c:=root589) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root590_contains : root590.Contains (rootPhase 590) := by
  have hh := CBox.mul_contains_g root295_contains root295_contains (c:=root590) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid591_contains : mid591.Contains (rootPhase 590) := root590_contains
lemma root591_contains : root591.Contains (rootPhase 591) := by
  have hh := CBox.mul_contains_g mid591_contains root1_contains (c:=root591) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root592_contains : root592.Contains (rootPhase 592) := by
  have hh := CBox.mul_contains_g root296_contains root296_contains (c:=root592) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid593_contains : mid593.Contains (rootPhase 592) := root592_contains
lemma root593_contains : root593.Contains (rootPhase 593) := by
  have hh := CBox.mul_contains_g mid593_contains root1_contains (c:=root593) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root594_contains : root594.Contains (rootPhase 594) := by
  have hh := CBox.mul_contains_g root297_contains root297_contains (c:=root594) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid595_contains : mid595.Contains (rootPhase 594) := root594_contains
lemma root595_contains : root595.Contains (rootPhase 595) := by
  have hh := CBox.mul_contains_g mid595_contains root1_contains (c:=root595) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root596_contains : root596.Contains (rootPhase 596) := by
  have hh := CBox.mul_contains_g root298_contains root298_contains (c:=root596) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid597_contains : mid597.Contains (rootPhase 596) := root596_contains
lemma root597_contains : root597.Contains (rootPhase 597) := by
  have hh := CBox.mul_contains_g mid597_contains root1_contains (c:=root597) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root598_contains : root598.Contains (rootPhase 598) := by
  have hh := CBox.mul_contains_g root299_contains root299_contains (c:=root598) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid599_contains : mid599.Contains (rootPhase 598) := root598_contains
lemma root599_contains : root599.Contains (rootPhase 599) := by
  have hh := CBox.mul_contains_g mid599_contains root1_contains (c:=root599) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root600_contains : root600.Contains (rootPhase 600) := by
  have hh := CBox.mul_contains_g root300_contains root300_contains (c:=root600) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid601_contains : mid601.Contains (rootPhase 600) := root600_contains
lemma root601_contains : root601.Contains (rootPhase 601) := by
  have hh := CBox.mul_contains_g mid601_contains root1_contains (c:=root601) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root602_contains : root602.Contains (rootPhase 602) := by
  have hh := CBox.mul_contains_g root301_contains root301_contains (c:=root602) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid603_contains : mid603.Contains (rootPhase 602) := root602_contains
lemma root603_contains : root603.Contains (rootPhase 603) := by
  have hh := CBox.mul_contains_g mid603_contains root1_contains (c:=root603) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root604_contains : root604.Contains (rootPhase 604) := by
  have hh := CBox.mul_contains_g root302_contains root302_contains (c:=root604) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid605_contains : mid605.Contains (rootPhase 604) := root604_contains
lemma root605_contains : root605.Contains (rootPhase 605) := by
  have hh := CBox.mul_contains_g mid605_contains root1_contains (c:=root605) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root606_contains : root606.Contains (rootPhase 606) := by
  have hh := CBox.mul_contains_g root303_contains root303_contains (c:=root606) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid607_contains : mid607.Contains (rootPhase 606) := root606_contains
lemma root607_contains : root607.Contains (rootPhase 607) := by
  have hh := CBox.mul_contains_g mid607_contains root1_contains (c:=root607) (by decide +kernel)
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
lemma roots18_contains_g_oai (j : Fin 32) : (roots18 j).Contains (rootPhase (576+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root576_contains
  · exact IntegerRoots.root577_contains
  · exact IntegerRoots.root578_contains
  · exact IntegerRoots.root579_contains
  · exact IntegerRoots.root580_contains
  · exact IntegerRoots.root581_contains
  · exact IntegerRoots.root582_contains
  · exact IntegerRoots.root583_contains
  · exact IntegerRoots.root584_contains
  · exact IntegerRoots.root585_contains
  · exact IntegerRoots.root586_contains
  · exact IntegerRoots.root587_contains
  · exact IntegerRoots.root588_contains
  · exact IntegerRoots.root589_contains
  · exact IntegerRoots.root590_contains
  · exact IntegerRoots.root591_contains
  · exact IntegerRoots.root592_contains
  · exact IntegerRoots.root593_contains
  · exact IntegerRoots.root594_contains
  · exact IntegerRoots.root595_contains
  · exact IntegerRoots.root596_contains
  · exact IntegerRoots.root597_contains
  · exact IntegerRoots.root598_contains
  · exact IntegerRoots.root599_contains
  · exact IntegerRoots.root600_contains
  · exact IntegerRoots.root601_contains
  · exact IntegerRoots.root602_contains
  · exact IntegerRoots.root603_contains
  · exact IntegerRoots.root604_contains
  · exact IntegerRoots.root605_contains
  · exact IntegerRoots.root606_contains
  · exact IntegerRoots.root607_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots18_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots18_contains_g_oai
