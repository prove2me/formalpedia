-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots8_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:07:41.990406+00:00
-- url     : https://prove2.me/submissions/76068668-1171-496b-875d-5a0274a720ba

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
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains_g root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid17_contains : mid17.Contains (rootPhase 16) := root16_contains
lemma root17_contains : root17.Contains (rootPhase 17) := by
  have hh := CBox.mul_contains_g mid17_contains root1_contains (c:=root17) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root32_contains : root32.Contains (rootPhase 32) := by
  have hh := CBox.mul_contains_g root16_contains root16_contains (c:=root32) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid33_contains : mid33.Contains (rootPhase 32) := root32_contains
lemma root33_contains : root33.Contains (rootPhase 33) := by
  have hh := CBox.mul_contains_g mid33_contains root1_contains (c:=root33) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root34_contains : root34.Contains (rootPhase 34) := by
  have hh := CBox.mul_contains_g root17_contains root17_contains (c:=root34) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid35_contains : mid35.Contains (rootPhase 34) := root34_contains
lemma root35_contains : root35.Contains (rootPhase 35) := by
  have hh := CBox.mul_contains_g mid35_contains root1_contains (c:=root35) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root64_contains : root64.Contains (rootPhase 64) := by
  have hh := CBox.mul_contains_g root32_contains root32_contains (c:=root64) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid65_contains : mid65.Contains (rootPhase 64) := root64_contains
lemma root65_contains : root65.Contains (rootPhase 65) := by
  have hh := CBox.mul_contains_g mid65_contains root1_contains (c:=root65) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root66_contains : root66.Contains (rootPhase 66) := by
  have hh := CBox.mul_contains_g root33_contains root33_contains (c:=root66) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid67_contains : mid67.Contains (rootPhase 66) := root66_contains
lemma root67_contains : root67.Contains (rootPhase 67) := by
  have hh := CBox.mul_contains_g mid67_contains root1_contains (c:=root67) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root68_contains : root68.Contains (rootPhase 68) := by
  have hh := CBox.mul_contains_g root34_contains root34_contains (c:=root68) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid69_contains : mid69.Contains (rootPhase 68) := root68_contains
lemma root69_contains : root69.Contains (rootPhase 69) := by
  have hh := CBox.mul_contains_g mid69_contains root1_contains (c:=root69) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root70_contains : root70.Contains (rootPhase 70) := by
  have hh := CBox.mul_contains_g root35_contains root35_contains (c:=root70) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid71_contains : mid71.Contains (rootPhase 70) := root70_contains
lemma root71_contains : root71.Contains (rootPhase 71) := by
  have hh := CBox.mul_contains_g mid71_contains root1_contains (c:=root71) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root128_contains : root128.Contains (rootPhase 128) := by
  have hh := CBox.mul_contains_g root64_contains root64_contains (c:=root128) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid129_contains : mid129.Contains (rootPhase 128) := root128_contains
lemma root129_contains : root129.Contains (rootPhase 129) := by
  have hh := CBox.mul_contains_g mid129_contains root1_contains (c:=root129) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root130_contains : root130.Contains (rootPhase 130) := by
  have hh := CBox.mul_contains_g root65_contains root65_contains (c:=root130) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid131_contains : mid131.Contains (rootPhase 130) := root130_contains
lemma root131_contains : root131.Contains (rootPhase 131) := by
  have hh := CBox.mul_contains_g mid131_contains root1_contains (c:=root131) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root132_contains : root132.Contains (rootPhase 132) := by
  have hh := CBox.mul_contains_g root66_contains root66_contains (c:=root132) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid133_contains : mid133.Contains (rootPhase 132) := root132_contains
lemma root133_contains : root133.Contains (rootPhase 133) := by
  have hh := CBox.mul_contains_g mid133_contains root1_contains (c:=root133) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root134_contains : root134.Contains (rootPhase 134) := by
  have hh := CBox.mul_contains_g root67_contains root67_contains (c:=root134) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid135_contains : mid135.Contains (rootPhase 134) := root134_contains
lemma root135_contains : root135.Contains (rootPhase 135) := by
  have hh := CBox.mul_contains_g mid135_contains root1_contains (c:=root135) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root136_contains : root136.Contains (rootPhase 136) := by
  have hh := CBox.mul_contains_g root68_contains root68_contains (c:=root136) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid137_contains : mid137.Contains (rootPhase 136) := root136_contains
lemma root137_contains : root137.Contains (rootPhase 137) := by
  have hh := CBox.mul_contains_g mid137_contains root1_contains (c:=root137) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root138_contains : root138.Contains (rootPhase 138) := by
  have hh := CBox.mul_contains_g root69_contains root69_contains (c:=root138) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid139_contains : mid139.Contains (rootPhase 138) := root138_contains
lemma root139_contains : root139.Contains (rootPhase 139) := by
  have hh := CBox.mul_contains_g mid139_contains root1_contains (c:=root139) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root140_contains : root140.Contains (rootPhase 140) := by
  have hh := CBox.mul_contains_g root70_contains root70_contains (c:=root140) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid141_contains : mid141.Contains (rootPhase 140) := root140_contains
lemma root141_contains : root141.Contains (rootPhase 141) := by
  have hh := CBox.mul_contains_g mid141_contains root1_contains (c:=root141) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root142_contains : root142.Contains (rootPhase 142) := by
  have hh := CBox.mul_contains_g root71_contains root71_contains (c:=root142) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid143_contains : mid143.Contains (rootPhase 142) := root142_contains
lemma root143_contains : root143.Contains (rootPhase 143) := by
  have hh := CBox.mul_contains_g mid143_contains root1_contains (c:=root143) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root256_contains : root256.Contains (rootPhase 256) := by
  have hh := CBox.mul_contains_g root128_contains root128_contains (c:=root256) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid257_contains : mid257.Contains (rootPhase 256) := root256_contains
lemma root257_contains : root257.Contains (rootPhase 257) := by
  have hh := CBox.mul_contains_g mid257_contains root1_contains (c:=root257) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root258_contains : root258.Contains (rootPhase 258) := by
  have hh := CBox.mul_contains_g root129_contains root129_contains (c:=root258) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid259_contains : mid259.Contains (rootPhase 258) := root258_contains
lemma root259_contains : root259.Contains (rootPhase 259) := by
  have hh := CBox.mul_contains_g mid259_contains root1_contains (c:=root259) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root260_contains : root260.Contains (rootPhase 260) := by
  have hh := CBox.mul_contains_g root130_contains root130_contains (c:=root260) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid261_contains : mid261.Contains (rootPhase 260) := root260_contains
lemma root261_contains : root261.Contains (rootPhase 261) := by
  have hh := CBox.mul_contains_g mid261_contains root1_contains (c:=root261) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root262_contains : root262.Contains (rootPhase 262) := by
  have hh := CBox.mul_contains_g root131_contains root131_contains (c:=root262) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid263_contains : mid263.Contains (rootPhase 262) := root262_contains
lemma root263_contains : root263.Contains (rootPhase 263) := by
  have hh := CBox.mul_contains_g mid263_contains root1_contains (c:=root263) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root264_contains : root264.Contains (rootPhase 264) := by
  have hh := CBox.mul_contains_g root132_contains root132_contains (c:=root264) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid265_contains : mid265.Contains (rootPhase 264) := root264_contains
lemma root265_contains : root265.Contains (rootPhase 265) := by
  have hh := CBox.mul_contains_g mid265_contains root1_contains (c:=root265) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root266_contains : root266.Contains (rootPhase 266) := by
  have hh := CBox.mul_contains_g root133_contains root133_contains (c:=root266) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid267_contains : mid267.Contains (rootPhase 266) := root266_contains
lemma root267_contains : root267.Contains (rootPhase 267) := by
  have hh := CBox.mul_contains_g mid267_contains root1_contains (c:=root267) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root268_contains : root268.Contains (rootPhase 268) := by
  have hh := CBox.mul_contains_g root134_contains root134_contains (c:=root268) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid269_contains : mid269.Contains (rootPhase 268) := root268_contains
lemma root269_contains : root269.Contains (rootPhase 269) := by
  have hh := CBox.mul_contains_g mid269_contains root1_contains (c:=root269) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root270_contains : root270.Contains (rootPhase 270) := by
  have hh := CBox.mul_contains_g root135_contains root135_contains (c:=root270) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid271_contains : mid271.Contains (rootPhase 270) := root270_contains
lemma root271_contains : root271.Contains (rootPhase 271) := by
  have hh := CBox.mul_contains_g mid271_contains root1_contains (c:=root271) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root272_contains : root272.Contains (rootPhase 272) := by
  have hh := CBox.mul_contains_g root136_contains root136_contains (c:=root272) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid273_contains : mid273.Contains (rootPhase 272) := root272_contains
lemma root273_contains : root273.Contains (rootPhase 273) := by
  have hh := CBox.mul_contains_g mid273_contains root1_contains (c:=root273) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root274_contains : root274.Contains (rootPhase 274) := by
  have hh := CBox.mul_contains_g root137_contains root137_contains (c:=root274) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid275_contains : mid275.Contains (rootPhase 274) := root274_contains
lemma root275_contains : root275.Contains (rootPhase 275) := by
  have hh := CBox.mul_contains_g mid275_contains root1_contains (c:=root275) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root276_contains : root276.Contains (rootPhase 276) := by
  have hh := CBox.mul_contains_g root138_contains root138_contains (c:=root276) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid277_contains : mid277.Contains (rootPhase 276) := root276_contains
lemma root277_contains : root277.Contains (rootPhase 277) := by
  have hh := CBox.mul_contains_g mid277_contains root1_contains (c:=root277) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root278_contains : root278.Contains (rootPhase 278) := by
  have hh := CBox.mul_contains_g root139_contains root139_contains (c:=root278) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid279_contains : mid279.Contains (rootPhase 278) := root278_contains
lemma root279_contains : root279.Contains (rootPhase 279) := by
  have hh := CBox.mul_contains_g mid279_contains root1_contains (c:=root279) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root280_contains : root280.Contains (rootPhase 280) := by
  have hh := CBox.mul_contains_g root140_contains root140_contains (c:=root280) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid281_contains : mid281.Contains (rootPhase 280) := root280_contains
lemma root281_contains : root281.Contains (rootPhase 281) := by
  have hh := CBox.mul_contains_g mid281_contains root1_contains (c:=root281) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root282_contains : root282.Contains (rootPhase 282) := by
  have hh := CBox.mul_contains_g root141_contains root141_contains (c:=root282) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid283_contains : mid283.Contains (rootPhase 282) := root282_contains
lemma root283_contains : root283.Contains (rootPhase 283) := by
  have hh := CBox.mul_contains_g mid283_contains root1_contains (c:=root283) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root284_contains : root284.Contains (rootPhase 284) := by
  have hh := CBox.mul_contains_g root142_contains root142_contains (c:=root284) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid285_contains : mid285.Contains (rootPhase 284) := root284_contains
lemma root285_contains : root285.Contains (rootPhase 285) := by
  have hh := CBox.mul_contains_g mid285_contains root1_contains (c:=root285) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root286_contains : root286.Contains (rootPhase 286) := by
  have hh := CBox.mul_contains_g root143_contains root143_contains (c:=root286) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid287_contains : mid287.Contains (rootPhase 286) := root286_contains
lemma root287_contains : root287.Contains (rootPhase 287) := by
  have hh := CBox.mul_contains_g mid287_contains root1_contains (c:=root287) (by decide +kernel)
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
lemma roots8_contains_g_oai (j : Fin 32) : (roots8 j).Contains (rootPhase (256+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root256_contains
  · exact IntegerRoots.root257_contains
  · exact IntegerRoots.root258_contains
  · exact IntegerRoots.root259_contains
  · exact IntegerRoots.root260_contains
  · exact IntegerRoots.root261_contains
  · exact IntegerRoots.root262_contains
  · exact IntegerRoots.root263_contains
  · exact IntegerRoots.root264_contains
  · exact IntegerRoots.root265_contains
  · exact IntegerRoots.root266_contains
  · exact IntegerRoots.root267_contains
  · exact IntegerRoots.root268_contains
  · exact IntegerRoots.root269_contains
  · exact IntegerRoots.root270_contains
  · exact IntegerRoots.root271_contains
  · exact IntegerRoots.root272_contains
  · exact IntegerRoots.root273_contains
  · exact IntegerRoots.root274_contains
  · exact IntegerRoots.root275_contains
  · exact IntegerRoots.root276_contains
  · exact IntegerRoots.root277_contains
  · exact IntegerRoots.root278_contains
  · exact IntegerRoots.root279_contains
  · exact IntegerRoots.root280_contains
  · exact IntegerRoots.root281_contains
  · exact IntegerRoots.root282_contains
  · exact IntegerRoots.root283_contains
  · exact IntegerRoots.root284_contains
  · exact IntegerRoots.root285_contains
  · exact IntegerRoots.root286_contains
  · exact IntegerRoots.root287_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots8_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots8_contains_g_oai
