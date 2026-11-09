-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots16_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:06:27.712203+00:00
-- url     : https://prove2.me/submissions/02e06a9f-7f2f-4ff3-b33b-cca744349e9f

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G065
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
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains_g root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains_g root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains_g root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root32_contains : root32.Contains (rootPhase 32) := by
  have hh := CBox.mul_contains_g root16_contains root16_contains (c:=root32) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid33_contains : mid33.Contains (rootPhase 32) := root32_contains
lemma root33_contains : root33.Contains (rootPhase 33) := by
  have hh := CBox.mul_contains_g mid33_contains root1_contains (c:=root33) (by decide +kernel)
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
lemma root512_contains : root512.Contains (rootPhase 512) := by
  have hh := CBox.mul_contains_g root256_contains root256_contains (c:=root512) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid513_contains : mid513.Contains (rootPhase 512) := root512_contains
lemma root513_contains : root513.Contains (rootPhase 513) := by
  have hh := CBox.mul_contains_g mid513_contains root1_contains (c:=root513) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root514_contains : root514.Contains (rootPhase 514) := by
  have hh := CBox.mul_contains_g root257_contains root257_contains (c:=root514) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid515_contains : mid515.Contains (rootPhase 514) := root514_contains
lemma root515_contains : root515.Contains (rootPhase 515) := by
  have hh := CBox.mul_contains_g mid515_contains root1_contains (c:=root515) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root516_contains : root516.Contains (rootPhase 516) := by
  have hh := CBox.mul_contains_g root258_contains root258_contains (c:=root516) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid517_contains : mid517.Contains (rootPhase 516) := root516_contains
lemma root517_contains : root517.Contains (rootPhase 517) := by
  have hh := CBox.mul_contains_g mid517_contains root1_contains (c:=root517) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root518_contains : root518.Contains (rootPhase 518) := by
  have hh := CBox.mul_contains_g root259_contains root259_contains (c:=root518) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid519_contains : mid519.Contains (rootPhase 518) := root518_contains
lemma root519_contains : root519.Contains (rootPhase 519) := by
  have hh := CBox.mul_contains_g mid519_contains root1_contains (c:=root519) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root520_contains : root520.Contains (rootPhase 520) := by
  have hh := CBox.mul_contains_g root260_contains root260_contains (c:=root520) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid521_contains : mid521.Contains (rootPhase 520) := root520_contains
lemma root521_contains : root521.Contains (rootPhase 521) := by
  have hh := CBox.mul_contains_g mid521_contains root1_contains (c:=root521) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root522_contains : root522.Contains (rootPhase 522) := by
  have hh := CBox.mul_contains_g root261_contains root261_contains (c:=root522) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid523_contains : mid523.Contains (rootPhase 522) := root522_contains
lemma root523_contains : root523.Contains (rootPhase 523) := by
  have hh := CBox.mul_contains_g mid523_contains root1_contains (c:=root523) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root524_contains : root524.Contains (rootPhase 524) := by
  have hh := CBox.mul_contains_g root262_contains root262_contains (c:=root524) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid525_contains : mid525.Contains (rootPhase 524) := root524_contains
lemma root525_contains : root525.Contains (rootPhase 525) := by
  have hh := CBox.mul_contains_g mid525_contains root1_contains (c:=root525) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root526_contains : root526.Contains (rootPhase 526) := by
  have hh := CBox.mul_contains_g root263_contains root263_contains (c:=root526) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid527_contains : mid527.Contains (rootPhase 526) := root526_contains
lemma root527_contains : root527.Contains (rootPhase 527) := by
  have hh := CBox.mul_contains_g mid527_contains root1_contains (c:=root527) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root528_contains : root528.Contains (rootPhase 528) := by
  have hh := CBox.mul_contains_g root264_contains root264_contains (c:=root528) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid529_contains : mid529.Contains (rootPhase 528) := root528_contains
lemma root529_contains : root529.Contains (rootPhase 529) := by
  have hh := CBox.mul_contains_g mid529_contains root1_contains (c:=root529) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root530_contains : root530.Contains (rootPhase 530) := by
  have hh := CBox.mul_contains_g root265_contains root265_contains (c:=root530) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid531_contains : mid531.Contains (rootPhase 530) := root530_contains
lemma root531_contains : root531.Contains (rootPhase 531) := by
  have hh := CBox.mul_contains_g mid531_contains root1_contains (c:=root531) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root532_contains : root532.Contains (rootPhase 532) := by
  have hh := CBox.mul_contains_g root266_contains root266_contains (c:=root532) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid533_contains : mid533.Contains (rootPhase 532) := root532_contains
lemma root533_contains : root533.Contains (rootPhase 533) := by
  have hh := CBox.mul_contains_g mid533_contains root1_contains (c:=root533) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root534_contains : root534.Contains (rootPhase 534) := by
  have hh := CBox.mul_contains_g root267_contains root267_contains (c:=root534) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid535_contains : mid535.Contains (rootPhase 534) := root534_contains
lemma root535_contains : root535.Contains (rootPhase 535) := by
  have hh := CBox.mul_contains_g mid535_contains root1_contains (c:=root535) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root536_contains : root536.Contains (rootPhase 536) := by
  have hh := CBox.mul_contains_g root268_contains root268_contains (c:=root536) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid537_contains : mid537.Contains (rootPhase 536) := root536_contains
lemma root537_contains : root537.Contains (rootPhase 537) := by
  have hh := CBox.mul_contains_g mid537_contains root1_contains (c:=root537) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root538_contains : root538.Contains (rootPhase 538) := by
  have hh := CBox.mul_contains_g root269_contains root269_contains (c:=root538) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid539_contains : mid539.Contains (rootPhase 538) := root538_contains
lemma root539_contains : root539.Contains (rootPhase 539) := by
  have hh := CBox.mul_contains_g mid539_contains root1_contains (c:=root539) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root540_contains : root540.Contains (rootPhase 540) := by
  have hh := CBox.mul_contains_g root270_contains root270_contains (c:=root540) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid541_contains : mid541.Contains (rootPhase 540) := root540_contains
lemma root541_contains : root541.Contains (rootPhase 541) := by
  have hh := CBox.mul_contains_g mid541_contains root1_contains (c:=root541) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root542_contains : root542.Contains (rootPhase 542) := by
  have hh := CBox.mul_contains_g root271_contains root271_contains (c:=root542) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid543_contains : mid543.Contains (rootPhase 542) := root542_contains
lemma root543_contains : root543.Contains (rootPhase 543) := by
  have hh := CBox.mul_contains_g mid543_contains root1_contains (c:=root543) (by decide +kernel)
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
lemma roots16_contains_g_oai (j : Fin 32) : (roots16 j).Contains (rootPhase (512+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root512_contains
  · exact IntegerRoots.root513_contains
  · exact IntegerRoots.root514_contains
  · exact IntegerRoots.root515_contains
  · exact IntegerRoots.root516_contains
  · exact IntegerRoots.root517_contains
  · exact IntegerRoots.root518_contains
  · exact IntegerRoots.root519_contains
  · exact IntegerRoots.root520_contains
  · exact IntegerRoots.root521_contains
  · exact IntegerRoots.root522_contains
  · exact IntegerRoots.root523_contains
  · exact IntegerRoots.root524_contains
  · exact IntegerRoots.root525_contains
  · exact IntegerRoots.root526_contains
  · exact IntegerRoots.root527_contains
  · exact IntegerRoots.root528_contains
  · exact IntegerRoots.root529_contains
  · exact IntegerRoots.root530_contains
  · exact IntegerRoots.root531_contains
  · exact IntegerRoots.root532_contains
  · exact IntegerRoots.root533_contains
  · exact IntegerRoots.root534_contains
  · exact IntegerRoots.root535_contains
  · exact IntegerRoots.root536_contains
  · exact IntegerRoots.root537_contains
  · exact IntegerRoots.root538_contains
  · exact IntegerRoots.root539_contains
  · exact IntegerRoots.root540_contains
  · exact IntegerRoots.root541_contains
  · exact IntegerRoots.root542_contains
  · exact IntegerRoots.root543_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots16_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots16_contains_g_oai
