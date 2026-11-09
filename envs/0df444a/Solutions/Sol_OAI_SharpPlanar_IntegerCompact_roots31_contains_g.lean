-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots31_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:32:15.1225+00:00
-- url     : https://prove2.me/submissions/8b359f40-e1e7-4a42-a607-5d51182561b1

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
lemma mid31_contains : mid31.Contains (rootPhase 30) := root30_contains
lemma root31_contains : root31.Contains (rootPhase 31) := by
  have hh := CBox.mul_contains_g mid31_contains root1_contains (c:=root31) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root62_contains : root62.Contains (rootPhase 62) := by
  have hh := CBox.mul_contains_g root31_contains root31_contains (c:=root62) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid63_contains : mid63.Contains (rootPhase 62) := root62_contains
lemma root63_contains : root63.Contains (rootPhase 63) := by
  have hh := CBox.mul_contains_g mid63_contains root1_contains (c:=root63) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root124_contains : root124.Contains (rootPhase 124) := by
  have hh := CBox.mul_contains_g root62_contains root62_contains (c:=root124) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid125_contains : mid125.Contains (rootPhase 124) := root124_contains
lemma root125_contains : root125.Contains (rootPhase 125) := by
  have hh := CBox.mul_contains_g mid125_contains root1_contains (c:=root125) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root126_contains : root126.Contains (rootPhase 126) := by
  have hh := CBox.mul_contains_g root63_contains root63_contains (c:=root126) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid127_contains : mid127.Contains (rootPhase 126) := root126_contains
lemma root127_contains : root127.Contains (rootPhase 127) := by
  have hh := CBox.mul_contains_g mid127_contains root1_contains (c:=root127) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root248_contains : root248.Contains (rootPhase 248) := by
  have hh := CBox.mul_contains_g root124_contains root124_contains (c:=root248) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid249_contains : mid249.Contains (rootPhase 248) := root248_contains
lemma root249_contains : root249.Contains (rootPhase 249) := by
  have hh := CBox.mul_contains_g mid249_contains root1_contains (c:=root249) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root250_contains : root250.Contains (rootPhase 250) := by
  have hh := CBox.mul_contains_g root125_contains root125_contains (c:=root250) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid251_contains : mid251.Contains (rootPhase 250) := root250_contains
lemma root251_contains : root251.Contains (rootPhase 251) := by
  have hh := CBox.mul_contains_g mid251_contains root1_contains (c:=root251) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root252_contains : root252.Contains (rootPhase 252) := by
  have hh := CBox.mul_contains_g root126_contains root126_contains (c:=root252) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid253_contains : mid253.Contains (rootPhase 252) := root252_contains
lemma root253_contains : root253.Contains (rootPhase 253) := by
  have hh := CBox.mul_contains_g mid253_contains root1_contains (c:=root253) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root254_contains : root254.Contains (rootPhase 254) := by
  have hh := CBox.mul_contains_g root127_contains root127_contains (c:=root254) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid255_contains : mid255.Contains (rootPhase 254) := root254_contains
lemma root255_contains : root255.Contains (rootPhase 255) := by
  have hh := CBox.mul_contains_g mid255_contains root1_contains (c:=root255) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root496_contains : root496.Contains (rootPhase 496) := by
  have hh := CBox.mul_contains_g root248_contains root248_contains (c:=root496) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid497_contains : mid497.Contains (rootPhase 496) := root496_contains
lemma root497_contains : root497.Contains (rootPhase 497) := by
  have hh := CBox.mul_contains_g mid497_contains root1_contains (c:=root497) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root498_contains : root498.Contains (rootPhase 498) := by
  have hh := CBox.mul_contains_g root249_contains root249_contains (c:=root498) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid499_contains : mid499.Contains (rootPhase 498) := root498_contains
lemma root499_contains : root499.Contains (rootPhase 499) := by
  have hh := CBox.mul_contains_g mid499_contains root1_contains (c:=root499) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root500_contains : root500.Contains (rootPhase 500) := by
  have hh := CBox.mul_contains_g root250_contains root250_contains (c:=root500) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid501_contains : mid501.Contains (rootPhase 500) := root500_contains
lemma root501_contains : root501.Contains (rootPhase 501) := by
  have hh := CBox.mul_contains_g mid501_contains root1_contains (c:=root501) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root502_contains : root502.Contains (rootPhase 502) := by
  have hh := CBox.mul_contains_g root251_contains root251_contains (c:=root502) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid503_contains : mid503.Contains (rootPhase 502) := root502_contains
lemma root503_contains : root503.Contains (rootPhase 503) := by
  have hh := CBox.mul_contains_g mid503_contains root1_contains (c:=root503) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root504_contains : root504.Contains (rootPhase 504) := by
  have hh := CBox.mul_contains_g root252_contains root252_contains (c:=root504) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid505_contains : mid505.Contains (rootPhase 504) := root504_contains
lemma root505_contains : root505.Contains (rootPhase 505) := by
  have hh := CBox.mul_contains_g mid505_contains root1_contains (c:=root505) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root506_contains : root506.Contains (rootPhase 506) := by
  have hh := CBox.mul_contains_g root253_contains root253_contains (c:=root506) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid507_contains : mid507.Contains (rootPhase 506) := root506_contains
lemma root507_contains : root507.Contains (rootPhase 507) := by
  have hh := CBox.mul_contains_g mid507_contains root1_contains (c:=root507) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root508_contains : root508.Contains (rootPhase 508) := by
  have hh := CBox.mul_contains_g root254_contains root254_contains (c:=root508) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid509_contains : mid509.Contains (rootPhase 508) := root508_contains
lemma root509_contains : root509.Contains (rootPhase 509) := by
  have hh := CBox.mul_contains_g mid509_contains root1_contains (c:=root509) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root510_contains : root510.Contains (rootPhase 510) := by
  have hh := CBox.mul_contains_g root255_contains root255_contains (c:=root510) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid511_contains : mid511.Contains (rootPhase 510) := root510_contains
lemma root511_contains : root511.Contains (rootPhase 511) := by
  have hh := CBox.mul_contains_g mid511_contains root1_contains (c:=root511) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root992_contains : root992.Contains (rootPhase 992) := by
  have hh := CBox.mul_contains_g root496_contains root496_contains (c:=root992) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid993_contains : mid993.Contains (rootPhase 992) := root992_contains
lemma root993_contains : root993.Contains (rootPhase 993) := by
  have hh := CBox.mul_contains_g mid993_contains root1_contains (c:=root993) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root994_contains : root994.Contains (rootPhase 994) := by
  have hh := CBox.mul_contains_g root497_contains root497_contains (c:=root994) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid995_contains : mid995.Contains (rootPhase 994) := root994_contains
lemma root995_contains : root995.Contains (rootPhase 995) := by
  have hh := CBox.mul_contains_g mid995_contains root1_contains (c:=root995) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root996_contains : root996.Contains (rootPhase 996) := by
  have hh := CBox.mul_contains_g root498_contains root498_contains (c:=root996) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid997_contains : mid997.Contains (rootPhase 996) := root996_contains
lemma root997_contains : root997.Contains (rootPhase 997) := by
  have hh := CBox.mul_contains_g mid997_contains root1_contains (c:=root997) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root998_contains : root998.Contains (rootPhase 998) := by
  have hh := CBox.mul_contains_g root499_contains root499_contains (c:=root998) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid999_contains : mid999.Contains (rootPhase 998) := root998_contains
lemma root999_contains : root999.Contains (rootPhase 999) := by
  have hh := CBox.mul_contains_g mid999_contains root1_contains (c:=root999) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1000_contains : root1000.Contains (rootPhase 1000) := by
  have hh := CBox.mul_contains_g root500_contains root500_contains (c:=root1000) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1001_contains : mid1001.Contains (rootPhase 1000) := root1000_contains
lemma root1001_contains : root1001.Contains (rootPhase 1001) := by
  have hh := CBox.mul_contains_g mid1001_contains root1_contains (c:=root1001) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1002_contains : root1002.Contains (rootPhase 1002) := by
  have hh := CBox.mul_contains_g root501_contains root501_contains (c:=root1002) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1003_contains : mid1003.Contains (rootPhase 1002) := root1002_contains
lemma root1003_contains : root1003.Contains (rootPhase 1003) := by
  have hh := CBox.mul_contains_g mid1003_contains root1_contains (c:=root1003) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1004_contains : root1004.Contains (rootPhase 1004) := by
  have hh := CBox.mul_contains_g root502_contains root502_contains (c:=root1004) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1005_contains : mid1005.Contains (rootPhase 1004) := root1004_contains
lemma root1005_contains : root1005.Contains (rootPhase 1005) := by
  have hh := CBox.mul_contains_g mid1005_contains root1_contains (c:=root1005) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1006_contains : root1006.Contains (rootPhase 1006) := by
  have hh := CBox.mul_contains_g root503_contains root503_contains (c:=root1006) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1007_contains : mid1007.Contains (rootPhase 1006) := root1006_contains
lemma root1007_contains : root1007.Contains (rootPhase 1007) := by
  have hh := CBox.mul_contains_g mid1007_contains root1_contains (c:=root1007) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1008_contains : root1008.Contains (rootPhase 1008) := by
  have hh := CBox.mul_contains_g root504_contains root504_contains (c:=root1008) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1009_contains : mid1009.Contains (rootPhase 1008) := root1008_contains
lemma root1009_contains : root1009.Contains (rootPhase 1009) := by
  have hh := CBox.mul_contains_g mid1009_contains root1_contains (c:=root1009) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1010_contains : root1010.Contains (rootPhase 1010) := by
  have hh := CBox.mul_contains_g root505_contains root505_contains (c:=root1010) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1011_contains : mid1011.Contains (rootPhase 1010) := root1010_contains
lemma root1011_contains : root1011.Contains (rootPhase 1011) := by
  have hh := CBox.mul_contains_g mid1011_contains root1_contains (c:=root1011) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1012_contains : root1012.Contains (rootPhase 1012) := by
  have hh := CBox.mul_contains_g root506_contains root506_contains (c:=root1012) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1013_contains : mid1013.Contains (rootPhase 1012) := root1012_contains
lemma root1013_contains : root1013.Contains (rootPhase 1013) := by
  have hh := CBox.mul_contains_g mid1013_contains root1_contains (c:=root1013) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1014_contains : root1014.Contains (rootPhase 1014) := by
  have hh := CBox.mul_contains_g root507_contains root507_contains (c:=root1014) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1015_contains : mid1015.Contains (rootPhase 1014) := root1014_contains
lemma root1015_contains : root1015.Contains (rootPhase 1015) := by
  have hh := CBox.mul_contains_g mid1015_contains root1_contains (c:=root1015) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1016_contains : root1016.Contains (rootPhase 1016) := by
  have hh := CBox.mul_contains_g root508_contains root508_contains (c:=root1016) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1017_contains : mid1017.Contains (rootPhase 1016) := root1016_contains
lemma root1017_contains : root1017.Contains (rootPhase 1017) := by
  have hh := CBox.mul_contains_g mid1017_contains root1_contains (c:=root1017) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1018_contains : root1018.Contains (rootPhase 1018) := by
  have hh := CBox.mul_contains_g root509_contains root509_contains (c:=root1018) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1019_contains : mid1019.Contains (rootPhase 1018) := root1018_contains
lemma root1019_contains : root1019.Contains (rootPhase 1019) := by
  have hh := CBox.mul_contains_g mid1019_contains root1_contains (c:=root1019) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1020_contains : root1020.Contains (rootPhase 1020) := by
  have hh := CBox.mul_contains_g root510_contains root510_contains (c:=root1020) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1021_contains : mid1021.Contains (rootPhase 1020) := root1020_contains
lemma root1021_contains : root1021.Contains (rootPhase 1021) := by
  have hh := CBox.mul_contains_g mid1021_contains root1_contains (c:=root1021) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1022_contains : root1022.Contains (rootPhase 1022) := by
  have hh := CBox.mul_contains_g root511_contains root511_contains (c:=root1022) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1023_contains : mid1023.Contains (rootPhase 1022) := root1022_contains
lemma root1023_contains : root1023.Contains (rootPhase 1023) := by
  have hh := CBox.mul_contains_g mid1023_contains root1_contains (c:=root1023) (by decide +kernel)
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
lemma roots31_contains_g_oai (j : Fin 32) : (roots31 j).Contains (rootPhase (992+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root992_contains
  · exact IntegerRoots.root993_contains
  · exact IntegerRoots.root994_contains
  · exact IntegerRoots.root995_contains
  · exact IntegerRoots.root996_contains
  · exact IntegerRoots.root997_contains
  · exact IntegerRoots.root998_contains
  · exact IntegerRoots.root999_contains
  · exact IntegerRoots.root1000_contains
  · exact IntegerRoots.root1001_contains
  · exact IntegerRoots.root1002_contains
  · exact IntegerRoots.root1003_contains
  · exact IntegerRoots.root1004_contains
  · exact IntegerRoots.root1005_contains
  · exact IntegerRoots.root1006_contains
  · exact IntegerRoots.root1007_contains
  · exact IntegerRoots.root1008_contains
  · exact IntegerRoots.root1009_contains
  · exact IntegerRoots.root1010_contains
  · exact IntegerRoots.root1011_contains
  · exact IntegerRoots.root1012_contains
  · exact IntegerRoots.root1013_contains
  · exact IntegerRoots.root1014_contains
  · exact IntegerRoots.root1015_contains
  · exact IntegerRoots.root1016_contains
  · exact IntegerRoots.root1017_contains
  · exact IntegerRoots.root1018_contains
  · exact IntegerRoots.root1019_contains
  · exact IntegerRoots.root1020_contains
  · exact IntegerRoots.root1021_contains
  · exact IntegerRoots.root1022_contains
  · exact IntegerRoots.root1023_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots31_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots31_contains_g_oai
