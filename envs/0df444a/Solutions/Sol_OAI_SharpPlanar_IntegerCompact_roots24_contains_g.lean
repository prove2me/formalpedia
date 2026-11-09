-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots24_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:13.527444+00:00
-- url     : https://prove2.me/submissions/0d712da7-80b6-4551-a5a0-aa1ec79a75e7

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G059
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G082
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G094
import Definitions.Def_OAIQ098G096
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
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains_g root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root48_contains : root48.Contains (rootPhase 48) := by
  have hh := CBox.mul_contains_g root24_contains root24_contains (c:=root48) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid49_contains : mid49.Contains (rootPhase 48) := root48_contains
lemma root49_contains : root49.Contains (rootPhase 49) := by
  have hh := CBox.mul_contains_g mid49_contains root1_contains (c:=root49) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root96_contains : root96.Contains (rootPhase 96) := by
  have hh := CBox.mul_contains_g root48_contains root48_contains (c:=root96) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid97_contains : mid97.Contains (rootPhase 96) := root96_contains
lemma root97_contains : root97.Contains (rootPhase 97) := by
  have hh := CBox.mul_contains_g mid97_contains root1_contains (c:=root97) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root98_contains : root98.Contains (rootPhase 98) := by
  have hh := CBox.mul_contains_g root49_contains root49_contains (c:=root98) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid99_contains : mid99.Contains (rootPhase 98) := root98_contains
lemma root99_contains : root99.Contains (rootPhase 99) := by
  have hh := CBox.mul_contains_g mid99_contains root1_contains (c:=root99) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root192_contains : root192.Contains (rootPhase 192) := by
  have hh := CBox.mul_contains_g root96_contains root96_contains (c:=root192) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid193_contains : mid193.Contains (rootPhase 192) := root192_contains
lemma root193_contains : root193.Contains (rootPhase 193) := by
  have hh := CBox.mul_contains_g mid193_contains root1_contains (c:=root193) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root194_contains : root194.Contains (rootPhase 194) := by
  have hh := CBox.mul_contains_g root97_contains root97_contains (c:=root194) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid195_contains : mid195.Contains (rootPhase 194) := root194_contains
lemma root195_contains : root195.Contains (rootPhase 195) := by
  have hh := CBox.mul_contains_g mid195_contains root1_contains (c:=root195) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root196_contains : root196.Contains (rootPhase 196) := by
  have hh := CBox.mul_contains_g root98_contains root98_contains (c:=root196) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid197_contains : mid197.Contains (rootPhase 196) := root196_contains
lemma root197_contains : root197.Contains (rootPhase 197) := by
  have hh := CBox.mul_contains_g mid197_contains root1_contains (c:=root197) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root198_contains : root198.Contains (rootPhase 198) := by
  have hh := CBox.mul_contains_g root99_contains root99_contains (c:=root198) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid199_contains : mid199.Contains (rootPhase 198) := root198_contains
lemma root199_contains : root199.Contains (rootPhase 199) := by
  have hh := CBox.mul_contains_g mid199_contains root1_contains (c:=root199) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root384_contains : root384.Contains (rootPhase 384) := by
  have hh := CBox.mul_contains_g root192_contains root192_contains (c:=root384) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid385_contains : mid385.Contains (rootPhase 384) := root384_contains
lemma root385_contains : root385.Contains (rootPhase 385) := by
  have hh := CBox.mul_contains_g mid385_contains root1_contains (c:=root385) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root386_contains : root386.Contains (rootPhase 386) := by
  have hh := CBox.mul_contains_g root193_contains root193_contains (c:=root386) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid387_contains : mid387.Contains (rootPhase 386) := root386_contains
lemma root387_contains : root387.Contains (rootPhase 387) := by
  have hh := CBox.mul_contains_g mid387_contains root1_contains (c:=root387) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root388_contains : root388.Contains (rootPhase 388) := by
  have hh := CBox.mul_contains_g root194_contains root194_contains (c:=root388) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid389_contains : mid389.Contains (rootPhase 388) := root388_contains
lemma root389_contains : root389.Contains (rootPhase 389) := by
  have hh := CBox.mul_contains_g mid389_contains root1_contains (c:=root389) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root390_contains : root390.Contains (rootPhase 390) := by
  have hh := CBox.mul_contains_g root195_contains root195_contains (c:=root390) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid391_contains : mid391.Contains (rootPhase 390) := root390_contains
lemma root391_contains : root391.Contains (rootPhase 391) := by
  have hh := CBox.mul_contains_g mid391_contains root1_contains (c:=root391) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root392_contains : root392.Contains (rootPhase 392) := by
  have hh := CBox.mul_contains_g root196_contains root196_contains (c:=root392) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid393_contains : mid393.Contains (rootPhase 392) := root392_contains
lemma root393_contains : root393.Contains (rootPhase 393) := by
  have hh := CBox.mul_contains_g mid393_contains root1_contains (c:=root393) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root394_contains : root394.Contains (rootPhase 394) := by
  have hh := CBox.mul_contains_g root197_contains root197_contains (c:=root394) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid395_contains : mid395.Contains (rootPhase 394) := root394_contains
lemma root395_contains : root395.Contains (rootPhase 395) := by
  have hh := CBox.mul_contains_g mid395_contains root1_contains (c:=root395) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root396_contains : root396.Contains (rootPhase 396) := by
  have hh := CBox.mul_contains_g root198_contains root198_contains (c:=root396) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid397_contains : mid397.Contains (rootPhase 396) := root396_contains
lemma root397_contains : root397.Contains (rootPhase 397) := by
  have hh := CBox.mul_contains_g mid397_contains root1_contains (c:=root397) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root398_contains : root398.Contains (rootPhase 398) := by
  have hh := CBox.mul_contains_g root199_contains root199_contains (c:=root398) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid399_contains : mid399.Contains (rootPhase 398) := root398_contains
lemma root399_contains : root399.Contains (rootPhase 399) := by
  have hh := CBox.mul_contains_g mid399_contains root1_contains (c:=root399) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root768_contains : root768.Contains (rootPhase 768) := by
  have hh := CBox.mul_contains_g root384_contains root384_contains (c:=root768) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid769_contains : mid769.Contains (rootPhase 768) := root768_contains
lemma root769_contains : root769.Contains (rootPhase 769) := by
  have hh := CBox.mul_contains_g mid769_contains root1_contains (c:=root769) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root770_contains : root770.Contains (rootPhase 770) := by
  have hh := CBox.mul_contains_g root385_contains root385_contains (c:=root770) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid771_contains : mid771.Contains (rootPhase 770) := root770_contains
lemma root771_contains : root771.Contains (rootPhase 771) := by
  have hh := CBox.mul_contains_g mid771_contains root1_contains (c:=root771) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root772_contains : root772.Contains (rootPhase 772) := by
  have hh := CBox.mul_contains_g root386_contains root386_contains (c:=root772) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid773_contains : mid773.Contains (rootPhase 772) := root772_contains
lemma root773_contains : root773.Contains (rootPhase 773) := by
  have hh := CBox.mul_contains_g mid773_contains root1_contains (c:=root773) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root774_contains : root774.Contains (rootPhase 774) := by
  have hh := CBox.mul_contains_g root387_contains root387_contains (c:=root774) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid775_contains : mid775.Contains (rootPhase 774) := root774_contains
lemma root775_contains : root775.Contains (rootPhase 775) := by
  have hh := CBox.mul_contains_g mid775_contains root1_contains (c:=root775) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root776_contains : root776.Contains (rootPhase 776) := by
  have hh := CBox.mul_contains_g root388_contains root388_contains (c:=root776) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid777_contains : mid777.Contains (rootPhase 776) := root776_contains
lemma root777_contains : root777.Contains (rootPhase 777) := by
  have hh := CBox.mul_contains_g mid777_contains root1_contains (c:=root777) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root778_contains : root778.Contains (rootPhase 778) := by
  have hh := CBox.mul_contains_g root389_contains root389_contains (c:=root778) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid779_contains : mid779.Contains (rootPhase 778) := root778_contains
lemma root779_contains : root779.Contains (rootPhase 779) := by
  have hh := CBox.mul_contains_g mid779_contains root1_contains (c:=root779) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root780_contains : root780.Contains (rootPhase 780) := by
  have hh := CBox.mul_contains_g root390_contains root390_contains (c:=root780) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid781_contains : mid781.Contains (rootPhase 780) := root780_contains
lemma root781_contains : root781.Contains (rootPhase 781) := by
  have hh := CBox.mul_contains_g mid781_contains root1_contains (c:=root781) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root782_contains : root782.Contains (rootPhase 782) := by
  have hh := CBox.mul_contains_g root391_contains root391_contains (c:=root782) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid783_contains : mid783.Contains (rootPhase 782) := root782_contains
lemma root783_contains : root783.Contains (rootPhase 783) := by
  have hh := CBox.mul_contains_g mid783_contains root1_contains (c:=root783) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root784_contains : root784.Contains (rootPhase 784) := by
  have hh := CBox.mul_contains_g root392_contains root392_contains (c:=root784) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid785_contains : mid785.Contains (rootPhase 784) := root784_contains
lemma root785_contains : root785.Contains (rootPhase 785) := by
  have hh := CBox.mul_contains_g mid785_contains root1_contains (c:=root785) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root786_contains : root786.Contains (rootPhase 786) := by
  have hh := CBox.mul_contains_g root393_contains root393_contains (c:=root786) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid787_contains : mid787.Contains (rootPhase 786) := root786_contains
lemma root787_contains : root787.Contains (rootPhase 787) := by
  have hh := CBox.mul_contains_g mid787_contains root1_contains (c:=root787) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root788_contains : root788.Contains (rootPhase 788) := by
  have hh := CBox.mul_contains_g root394_contains root394_contains (c:=root788) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid789_contains : mid789.Contains (rootPhase 788) := root788_contains
lemma root789_contains : root789.Contains (rootPhase 789) := by
  have hh := CBox.mul_contains_g mid789_contains root1_contains (c:=root789) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root790_contains : root790.Contains (rootPhase 790) := by
  have hh := CBox.mul_contains_g root395_contains root395_contains (c:=root790) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid791_contains : mid791.Contains (rootPhase 790) := root790_contains
lemma root791_contains : root791.Contains (rootPhase 791) := by
  have hh := CBox.mul_contains_g mid791_contains root1_contains (c:=root791) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root792_contains : root792.Contains (rootPhase 792) := by
  have hh := CBox.mul_contains_g root396_contains root396_contains (c:=root792) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid793_contains : mid793.Contains (rootPhase 792) := root792_contains
lemma root793_contains : root793.Contains (rootPhase 793) := by
  have hh := CBox.mul_contains_g mid793_contains root1_contains (c:=root793) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root794_contains : root794.Contains (rootPhase 794) := by
  have hh := CBox.mul_contains_g root397_contains root397_contains (c:=root794) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid795_contains : mid795.Contains (rootPhase 794) := root794_contains
lemma root795_contains : root795.Contains (rootPhase 795) := by
  have hh := CBox.mul_contains_g mid795_contains root1_contains (c:=root795) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root796_contains : root796.Contains (rootPhase 796) := by
  have hh := CBox.mul_contains_g root398_contains root398_contains (c:=root796) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid797_contains : mid797.Contains (rootPhase 796) := root796_contains
lemma root797_contains : root797.Contains (rootPhase 797) := by
  have hh := CBox.mul_contains_g mid797_contains root1_contains (c:=root797) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root798_contains : root798.Contains (rootPhase 798) := by
  have hh := CBox.mul_contains_g root399_contains root399_contains (c:=root798) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid799_contains : mid799.Contains (rootPhase 798) := root798_contains
lemma root799_contains : root799.Contains (rootPhase 799) := by
  have hh := CBox.mul_contains_g mid799_contains root1_contains (c:=root799) (by decide +kernel)
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
lemma roots24_contains_g_oai (j : Fin 32) : (roots24 j).Contains (rootPhase (768+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root768_contains
  · exact IntegerRoots.root769_contains
  · exact IntegerRoots.root770_contains
  · exact IntegerRoots.root771_contains
  · exact IntegerRoots.root772_contains
  · exact IntegerRoots.root773_contains
  · exact IntegerRoots.root774_contains
  · exact IntegerRoots.root775_contains
  · exact IntegerRoots.root776_contains
  · exact IntegerRoots.root777_contains
  · exact IntegerRoots.root778_contains
  · exact IntegerRoots.root779_contains
  · exact IntegerRoots.root780_contains
  · exact IntegerRoots.root781_contains
  · exact IntegerRoots.root782_contains
  · exact IntegerRoots.root783_contains
  · exact IntegerRoots.root784_contains
  · exact IntegerRoots.root785_contains
  · exact IntegerRoots.root786_contains
  · exact IntegerRoots.root787_contains
  · exact IntegerRoots.root788_contains
  · exact IntegerRoots.root789_contains
  · exact IntegerRoots.root790_contains
  · exact IntegerRoots.root791_contains
  · exact IntegerRoots.root792_contains
  · exact IntegerRoots.root793_contains
  · exact IntegerRoots.root794_contains
  · exact IntegerRoots.root795_contains
  · exact IntegerRoots.root796_contains
  · exact IntegerRoots.root797_contains
  · exact IntegerRoots.root798_contains
  · exact IntegerRoots.root799_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots24_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots24_contains_g_oai
