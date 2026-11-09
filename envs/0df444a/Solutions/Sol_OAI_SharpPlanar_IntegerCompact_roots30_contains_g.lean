-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots30_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:48.099495+00:00
-- url     : https://prove2.me/submissions/49d61792-7fc2-4abb-be62-307eef90754a

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
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains_g mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains_g root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid7_contains : mid7.Contains (rootPhase 6) := root6_contains
lemma root7_contains : root7.Contains (rootPhase 7) := by
  have hh := CBox.mul_contains_g mid7_contains root1_contains (c:=root7) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root14_contains : root14.Contains (rootPhase 14) := by
  have hh := CBox.mul_contains_g root7_contains root7_contains (c:=root14) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid15_contains : mid15.Contains (rootPhase 14) := root14_contains
lemma root15_contains : root15.Contains (rootPhase 15) := by
  have hh := CBox.mul_contains_g mid15_contains root1_contains (c:=root15) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root30_contains : root30.Contains (rootPhase 30) := by
  have hh := CBox.mul_contains_g root15_contains root15_contains (c:=root30) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root60_contains : root60.Contains (rootPhase 60) := by
  have hh := CBox.mul_contains_g root30_contains root30_contains (c:=root60) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid61_contains : mid61.Contains (rootPhase 60) := root60_contains
lemma root61_contains : root61.Contains (rootPhase 61) := by
  have hh := CBox.mul_contains_g mid61_contains root1_contains (c:=root61) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root120_contains : root120.Contains (rootPhase 120) := by
  have hh := CBox.mul_contains_g root60_contains root60_contains (c:=root120) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid121_contains : mid121.Contains (rootPhase 120) := root120_contains
lemma root121_contains : root121.Contains (rootPhase 121) := by
  have hh := CBox.mul_contains_g mid121_contains root1_contains (c:=root121) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root122_contains : root122.Contains (rootPhase 122) := by
  have hh := CBox.mul_contains_g root61_contains root61_contains (c:=root122) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid123_contains : mid123.Contains (rootPhase 122) := root122_contains
lemma root123_contains : root123.Contains (rootPhase 123) := by
  have hh := CBox.mul_contains_g mid123_contains root1_contains (c:=root123) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root240_contains : root240.Contains (rootPhase 240) := by
  have hh := CBox.mul_contains_g root120_contains root120_contains (c:=root240) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid241_contains : mid241.Contains (rootPhase 240) := root240_contains
lemma root241_contains : root241.Contains (rootPhase 241) := by
  have hh := CBox.mul_contains_g mid241_contains root1_contains (c:=root241) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root242_contains : root242.Contains (rootPhase 242) := by
  have hh := CBox.mul_contains_g root121_contains root121_contains (c:=root242) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid243_contains : mid243.Contains (rootPhase 242) := root242_contains
lemma root243_contains : root243.Contains (rootPhase 243) := by
  have hh := CBox.mul_contains_g mid243_contains root1_contains (c:=root243) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root244_contains : root244.Contains (rootPhase 244) := by
  have hh := CBox.mul_contains_g root122_contains root122_contains (c:=root244) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid245_contains : mid245.Contains (rootPhase 244) := root244_contains
lemma root245_contains : root245.Contains (rootPhase 245) := by
  have hh := CBox.mul_contains_g mid245_contains root1_contains (c:=root245) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root246_contains : root246.Contains (rootPhase 246) := by
  have hh := CBox.mul_contains_g root123_contains root123_contains (c:=root246) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid247_contains : mid247.Contains (rootPhase 246) := root246_contains
lemma root247_contains : root247.Contains (rootPhase 247) := by
  have hh := CBox.mul_contains_g mid247_contains root1_contains (c:=root247) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root480_contains : root480.Contains (rootPhase 480) := by
  have hh := CBox.mul_contains_g root240_contains root240_contains (c:=root480) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid481_contains : mid481.Contains (rootPhase 480) := root480_contains
lemma root481_contains : root481.Contains (rootPhase 481) := by
  have hh := CBox.mul_contains_g mid481_contains root1_contains (c:=root481) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root482_contains : root482.Contains (rootPhase 482) := by
  have hh := CBox.mul_contains_g root241_contains root241_contains (c:=root482) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid483_contains : mid483.Contains (rootPhase 482) := root482_contains
lemma root483_contains : root483.Contains (rootPhase 483) := by
  have hh := CBox.mul_contains_g mid483_contains root1_contains (c:=root483) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root484_contains : root484.Contains (rootPhase 484) := by
  have hh := CBox.mul_contains_g root242_contains root242_contains (c:=root484) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid485_contains : mid485.Contains (rootPhase 484) := root484_contains
lemma root485_contains : root485.Contains (rootPhase 485) := by
  have hh := CBox.mul_contains_g mid485_contains root1_contains (c:=root485) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root486_contains : root486.Contains (rootPhase 486) := by
  have hh := CBox.mul_contains_g root243_contains root243_contains (c:=root486) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid487_contains : mid487.Contains (rootPhase 486) := root486_contains
lemma root487_contains : root487.Contains (rootPhase 487) := by
  have hh := CBox.mul_contains_g mid487_contains root1_contains (c:=root487) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root488_contains : root488.Contains (rootPhase 488) := by
  have hh := CBox.mul_contains_g root244_contains root244_contains (c:=root488) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid489_contains : mid489.Contains (rootPhase 488) := root488_contains
lemma root489_contains : root489.Contains (rootPhase 489) := by
  have hh := CBox.mul_contains_g mid489_contains root1_contains (c:=root489) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root490_contains : root490.Contains (rootPhase 490) := by
  have hh := CBox.mul_contains_g root245_contains root245_contains (c:=root490) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid491_contains : mid491.Contains (rootPhase 490) := root490_contains
lemma root491_contains : root491.Contains (rootPhase 491) := by
  have hh := CBox.mul_contains_g mid491_contains root1_contains (c:=root491) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root492_contains : root492.Contains (rootPhase 492) := by
  have hh := CBox.mul_contains_g root246_contains root246_contains (c:=root492) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid493_contains : mid493.Contains (rootPhase 492) := root492_contains
lemma root493_contains : root493.Contains (rootPhase 493) := by
  have hh := CBox.mul_contains_g mid493_contains root1_contains (c:=root493) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root494_contains : root494.Contains (rootPhase 494) := by
  have hh := CBox.mul_contains_g root247_contains root247_contains (c:=root494) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid495_contains : mid495.Contains (rootPhase 494) := root494_contains
lemma root495_contains : root495.Contains (rootPhase 495) := by
  have hh := CBox.mul_contains_g mid495_contains root1_contains (c:=root495) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root960_contains : root960.Contains (rootPhase 960) := by
  have hh := CBox.mul_contains_g root480_contains root480_contains (c:=root960) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid961_contains : mid961.Contains (rootPhase 960) := root960_contains
lemma root961_contains : root961.Contains (rootPhase 961) := by
  have hh := CBox.mul_contains_g mid961_contains root1_contains (c:=root961) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root962_contains : root962.Contains (rootPhase 962) := by
  have hh := CBox.mul_contains_g root481_contains root481_contains (c:=root962) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid963_contains : mid963.Contains (rootPhase 962) := root962_contains
lemma root963_contains : root963.Contains (rootPhase 963) := by
  have hh := CBox.mul_contains_g mid963_contains root1_contains (c:=root963) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root964_contains : root964.Contains (rootPhase 964) := by
  have hh := CBox.mul_contains_g root482_contains root482_contains (c:=root964) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid965_contains : mid965.Contains (rootPhase 964) := root964_contains
lemma root965_contains : root965.Contains (rootPhase 965) := by
  have hh := CBox.mul_contains_g mid965_contains root1_contains (c:=root965) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root966_contains : root966.Contains (rootPhase 966) := by
  have hh := CBox.mul_contains_g root483_contains root483_contains (c:=root966) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid967_contains : mid967.Contains (rootPhase 966) := root966_contains
lemma root967_contains : root967.Contains (rootPhase 967) := by
  have hh := CBox.mul_contains_g mid967_contains root1_contains (c:=root967) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root968_contains : root968.Contains (rootPhase 968) := by
  have hh := CBox.mul_contains_g root484_contains root484_contains (c:=root968) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid969_contains : mid969.Contains (rootPhase 968) := root968_contains
lemma root969_contains : root969.Contains (rootPhase 969) := by
  have hh := CBox.mul_contains_g mid969_contains root1_contains (c:=root969) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root970_contains : root970.Contains (rootPhase 970) := by
  have hh := CBox.mul_contains_g root485_contains root485_contains (c:=root970) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid971_contains : mid971.Contains (rootPhase 970) := root970_contains
lemma root971_contains : root971.Contains (rootPhase 971) := by
  have hh := CBox.mul_contains_g mid971_contains root1_contains (c:=root971) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root972_contains : root972.Contains (rootPhase 972) := by
  have hh := CBox.mul_contains_g root486_contains root486_contains (c:=root972) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid973_contains : mid973.Contains (rootPhase 972) := root972_contains
lemma root973_contains : root973.Contains (rootPhase 973) := by
  have hh := CBox.mul_contains_g mid973_contains root1_contains (c:=root973) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root974_contains : root974.Contains (rootPhase 974) := by
  have hh := CBox.mul_contains_g root487_contains root487_contains (c:=root974) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid975_contains : mid975.Contains (rootPhase 974) := root974_contains
lemma root975_contains : root975.Contains (rootPhase 975) := by
  have hh := CBox.mul_contains_g mid975_contains root1_contains (c:=root975) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root976_contains : root976.Contains (rootPhase 976) := by
  have hh := CBox.mul_contains_g root488_contains root488_contains (c:=root976) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid977_contains : mid977.Contains (rootPhase 976) := root976_contains
lemma root977_contains : root977.Contains (rootPhase 977) := by
  have hh := CBox.mul_contains_g mid977_contains root1_contains (c:=root977) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root978_contains : root978.Contains (rootPhase 978) := by
  have hh := CBox.mul_contains_g root489_contains root489_contains (c:=root978) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid979_contains : mid979.Contains (rootPhase 978) := root978_contains
lemma root979_contains : root979.Contains (rootPhase 979) := by
  have hh := CBox.mul_contains_g mid979_contains root1_contains (c:=root979) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root980_contains : root980.Contains (rootPhase 980) := by
  have hh := CBox.mul_contains_g root490_contains root490_contains (c:=root980) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid981_contains : mid981.Contains (rootPhase 980) := root980_contains
lemma root981_contains : root981.Contains (rootPhase 981) := by
  have hh := CBox.mul_contains_g mid981_contains root1_contains (c:=root981) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root982_contains : root982.Contains (rootPhase 982) := by
  have hh := CBox.mul_contains_g root491_contains root491_contains (c:=root982) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid983_contains : mid983.Contains (rootPhase 982) := root982_contains
lemma root983_contains : root983.Contains (rootPhase 983) := by
  have hh := CBox.mul_contains_g mid983_contains root1_contains (c:=root983) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root984_contains : root984.Contains (rootPhase 984) := by
  have hh := CBox.mul_contains_g root492_contains root492_contains (c:=root984) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid985_contains : mid985.Contains (rootPhase 984) := root984_contains
lemma root985_contains : root985.Contains (rootPhase 985) := by
  have hh := CBox.mul_contains_g mid985_contains root1_contains (c:=root985) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root986_contains : root986.Contains (rootPhase 986) := by
  have hh := CBox.mul_contains_g root493_contains root493_contains (c:=root986) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid987_contains : mid987.Contains (rootPhase 986) := root986_contains
lemma root987_contains : root987.Contains (rootPhase 987) := by
  have hh := CBox.mul_contains_g mid987_contains root1_contains (c:=root987) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root988_contains : root988.Contains (rootPhase 988) := by
  have hh := CBox.mul_contains_g root494_contains root494_contains (c:=root988) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid989_contains : mid989.Contains (rootPhase 988) := root988_contains
lemma root989_contains : root989.Contains (rootPhase 989) := by
  have hh := CBox.mul_contains_g mid989_contains root1_contains (c:=root989) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root990_contains : root990.Contains (rootPhase 990) := by
  have hh := CBox.mul_contains_g root495_contains root495_contains (c:=root990) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid991_contains : mid991.Contains (rootPhase 990) := root990_contains
lemma root991_contains : root991.Contains (rootPhase 991) := by
  have hh := CBox.mul_contains_g mid991_contains root1_contains (c:=root991) (by decide +kernel)
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
lemma roots30_contains_g_oai (j : Fin 32) : (roots30 j).Contains (rootPhase (960+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root960_contains
  · exact IntegerRoots.root961_contains
  · exact IntegerRoots.root962_contains
  · exact IntegerRoots.root963_contains
  · exact IntegerRoots.root964_contains
  · exact IntegerRoots.root965_contains
  · exact IntegerRoots.root966_contains
  · exact IntegerRoots.root967_contains
  · exact IntegerRoots.root968_contains
  · exact IntegerRoots.root969_contains
  · exact IntegerRoots.root970_contains
  · exact IntegerRoots.root971_contains
  · exact IntegerRoots.root972_contains
  · exact IntegerRoots.root973_contains
  · exact IntegerRoots.root974_contains
  · exact IntegerRoots.root975_contains
  · exact IntegerRoots.root976_contains
  · exact IntegerRoots.root977_contains
  · exact IntegerRoots.root978_contains
  · exact IntegerRoots.root979_contains
  · exact IntegerRoots.root980_contains
  · exact IntegerRoots.root981_contains
  · exact IntegerRoots.root982_contains
  · exact IntegerRoots.root983_contains
  · exact IntegerRoots.root984_contains
  · exact IntegerRoots.root985_contains
  · exact IntegerRoots.root986_contains
  · exact IntegerRoots.root987_contains
  · exact IntegerRoots.root988_contains
  · exact IntegerRoots.root989_contains
  · exact IntegerRoots.root990_contains
  · exact IntegerRoots.root991_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots30_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots30_contains_g_oai
