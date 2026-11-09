-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots29_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:46.712781+00:00
-- url     : https://prove2.me/submissions/70af8c04-d082-4f49-b6b3-15e6e8a88195

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
lemma root28_contains : root28.Contains (rootPhase 28) := by
  have hh := CBox.mul_contains_g root14_contains root14_contains (c:=root28) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid29_contains : mid29.Contains (rootPhase 28) := root28_contains
lemma root29_contains : root29.Contains (rootPhase 29) := by
  have hh := CBox.mul_contains_g mid29_contains root1_contains (c:=root29) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root58_contains : root58.Contains (rootPhase 58) := by
  have hh := CBox.mul_contains_g root29_contains root29_contains (c:=root58) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid59_contains : mid59.Contains (rootPhase 58) := root58_contains
lemma root59_contains : root59.Contains (rootPhase 59) := by
  have hh := CBox.mul_contains_g mid59_contains root1_contains (c:=root59) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root116_contains : root116.Contains (rootPhase 116) := by
  have hh := CBox.mul_contains_g root58_contains root58_contains (c:=root116) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid117_contains : mid117.Contains (rootPhase 116) := root116_contains
lemma root117_contains : root117.Contains (rootPhase 117) := by
  have hh := CBox.mul_contains_g mid117_contains root1_contains (c:=root117) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root118_contains : root118.Contains (rootPhase 118) := by
  have hh := CBox.mul_contains_g root59_contains root59_contains (c:=root118) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid119_contains : mid119.Contains (rootPhase 118) := root118_contains
lemma root119_contains : root119.Contains (rootPhase 119) := by
  have hh := CBox.mul_contains_g mid119_contains root1_contains (c:=root119) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root232_contains : root232.Contains (rootPhase 232) := by
  have hh := CBox.mul_contains_g root116_contains root116_contains (c:=root232) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid233_contains : mid233.Contains (rootPhase 232) := root232_contains
lemma root233_contains : root233.Contains (rootPhase 233) := by
  have hh := CBox.mul_contains_g mid233_contains root1_contains (c:=root233) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root234_contains : root234.Contains (rootPhase 234) := by
  have hh := CBox.mul_contains_g root117_contains root117_contains (c:=root234) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid235_contains : mid235.Contains (rootPhase 234) := root234_contains
lemma root235_contains : root235.Contains (rootPhase 235) := by
  have hh := CBox.mul_contains_g mid235_contains root1_contains (c:=root235) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root236_contains : root236.Contains (rootPhase 236) := by
  have hh := CBox.mul_contains_g root118_contains root118_contains (c:=root236) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid237_contains : mid237.Contains (rootPhase 236) := root236_contains
lemma root237_contains : root237.Contains (rootPhase 237) := by
  have hh := CBox.mul_contains_g mid237_contains root1_contains (c:=root237) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root238_contains : root238.Contains (rootPhase 238) := by
  have hh := CBox.mul_contains_g root119_contains root119_contains (c:=root238) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid239_contains : mid239.Contains (rootPhase 238) := root238_contains
lemma root239_contains : root239.Contains (rootPhase 239) := by
  have hh := CBox.mul_contains_g mid239_contains root1_contains (c:=root239) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root464_contains : root464.Contains (rootPhase 464) := by
  have hh := CBox.mul_contains_g root232_contains root232_contains (c:=root464) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid465_contains : mid465.Contains (rootPhase 464) := root464_contains
lemma root465_contains : root465.Contains (rootPhase 465) := by
  have hh := CBox.mul_contains_g mid465_contains root1_contains (c:=root465) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root466_contains : root466.Contains (rootPhase 466) := by
  have hh := CBox.mul_contains_g root233_contains root233_contains (c:=root466) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid467_contains : mid467.Contains (rootPhase 466) := root466_contains
lemma root467_contains : root467.Contains (rootPhase 467) := by
  have hh := CBox.mul_contains_g mid467_contains root1_contains (c:=root467) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root468_contains : root468.Contains (rootPhase 468) := by
  have hh := CBox.mul_contains_g root234_contains root234_contains (c:=root468) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid469_contains : mid469.Contains (rootPhase 468) := root468_contains
lemma root469_contains : root469.Contains (rootPhase 469) := by
  have hh := CBox.mul_contains_g mid469_contains root1_contains (c:=root469) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root470_contains : root470.Contains (rootPhase 470) := by
  have hh := CBox.mul_contains_g root235_contains root235_contains (c:=root470) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid471_contains : mid471.Contains (rootPhase 470) := root470_contains
lemma root471_contains : root471.Contains (rootPhase 471) := by
  have hh := CBox.mul_contains_g mid471_contains root1_contains (c:=root471) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root472_contains : root472.Contains (rootPhase 472) := by
  have hh := CBox.mul_contains_g root236_contains root236_contains (c:=root472) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid473_contains : mid473.Contains (rootPhase 472) := root472_contains
lemma root473_contains : root473.Contains (rootPhase 473) := by
  have hh := CBox.mul_contains_g mid473_contains root1_contains (c:=root473) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root474_contains : root474.Contains (rootPhase 474) := by
  have hh := CBox.mul_contains_g root237_contains root237_contains (c:=root474) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid475_contains : mid475.Contains (rootPhase 474) := root474_contains
lemma root475_contains : root475.Contains (rootPhase 475) := by
  have hh := CBox.mul_contains_g mid475_contains root1_contains (c:=root475) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root476_contains : root476.Contains (rootPhase 476) := by
  have hh := CBox.mul_contains_g root238_contains root238_contains (c:=root476) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid477_contains : mid477.Contains (rootPhase 476) := root476_contains
lemma root477_contains : root477.Contains (rootPhase 477) := by
  have hh := CBox.mul_contains_g mid477_contains root1_contains (c:=root477) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root478_contains : root478.Contains (rootPhase 478) := by
  have hh := CBox.mul_contains_g root239_contains root239_contains (c:=root478) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid479_contains : mid479.Contains (rootPhase 478) := root478_contains
lemma root479_contains : root479.Contains (rootPhase 479) := by
  have hh := CBox.mul_contains_g mid479_contains root1_contains (c:=root479) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root928_contains : root928.Contains (rootPhase 928) := by
  have hh := CBox.mul_contains_g root464_contains root464_contains (c:=root928) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid929_contains : mid929.Contains (rootPhase 928) := root928_contains
lemma root929_contains : root929.Contains (rootPhase 929) := by
  have hh := CBox.mul_contains_g mid929_contains root1_contains (c:=root929) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root930_contains : root930.Contains (rootPhase 930) := by
  have hh := CBox.mul_contains_g root465_contains root465_contains (c:=root930) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid931_contains : mid931.Contains (rootPhase 930) := root930_contains
lemma root931_contains : root931.Contains (rootPhase 931) := by
  have hh := CBox.mul_contains_g mid931_contains root1_contains (c:=root931) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root932_contains : root932.Contains (rootPhase 932) := by
  have hh := CBox.mul_contains_g root466_contains root466_contains (c:=root932) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid933_contains : mid933.Contains (rootPhase 932) := root932_contains
lemma root933_contains : root933.Contains (rootPhase 933) := by
  have hh := CBox.mul_contains_g mid933_contains root1_contains (c:=root933) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root934_contains : root934.Contains (rootPhase 934) := by
  have hh := CBox.mul_contains_g root467_contains root467_contains (c:=root934) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid935_contains : mid935.Contains (rootPhase 934) := root934_contains
lemma root935_contains : root935.Contains (rootPhase 935) := by
  have hh := CBox.mul_contains_g mid935_contains root1_contains (c:=root935) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root936_contains : root936.Contains (rootPhase 936) := by
  have hh := CBox.mul_contains_g root468_contains root468_contains (c:=root936) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid937_contains : mid937.Contains (rootPhase 936) := root936_contains
lemma root937_contains : root937.Contains (rootPhase 937) := by
  have hh := CBox.mul_contains_g mid937_contains root1_contains (c:=root937) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root938_contains : root938.Contains (rootPhase 938) := by
  have hh := CBox.mul_contains_g root469_contains root469_contains (c:=root938) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid939_contains : mid939.Contains (rootPhase 938) := root938_contains
lemma root939_contains : root939.Contains (rootPhase 939) := by
  have hh := CBox.mul_contains_g mid939_contains root1_contains (c:=root939) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root940_contains : root940.Contains (rootPhase 940) := by
  have hh := CBox.mul_contains_g root470_contains root470_contains (c:=root940) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid941_contains : mid941.Contains (rootPhase 940) := root940_contains
lemma root941_contains : root941.Contains (rootPhase 941) := by
  have hh := CBox.mul_contains_g mid941_contains root1_contains (c:=root941) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root942_contains : root942.Contains (rootPhase 942) := by
  have hh := CBox.mul_contains_g root471_contains root471_contains (c:=root942) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid943_contains : mid943.Contains (rootPhase 942) := root942_contains
lemma root943_contains : root943.Contains (rootPhase 943) := by
  have hh := CBox.mul_contains_g mid943_contains root1_contains (c:=root943) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root944_contains : root944.Contains (rootPhase 944) := by
  have hh := CBox.mul_contains_g root472_contains root472_contains (c:=root944) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid945_contains : mid945.Contains (rootPhase 944) := root944_contains
lemma root945_contains : root945.Contains (rootPhase 945) := by
  have hh := CBox.mul_contains_g mid945_contains root1_contains (c:=root945) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root946_contains : root946.Contains (rootPhase 946) := by
  have hh := CBox.mul_contains_g root473_contains root473_contains (c:=root946) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid947_contains : mid947.Contains (rootPhase 946) := root946_contains
lemma root947_contains : root947.Contains (rootPhase 947) := by
  have hh := CBox.mul_contains_g mid947_contains root1_contains (c:=root947) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root948_contains : root948.Contains (rootPhase 948) := by
  have hh := CBox.mul_contains_g root474_contains root474_contains (c:=root948) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid949_contains : mid949.Contains (rootPhase 948) := root948_contains
lemma root949_contains : root949.Contains (rootPhase 949) := by
  have hh := CBox.mul_contains_g mid949_contains root1_contains (c:=root949) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root950_contains : root950.Contains (rootPhase 950) := by
  have hh := CBox.mul_contains_g root475_contains root475_contains (c:=root950) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid951_contains : mid951.Contains (rootPhase 950) := root950_contains
lemma root951_contains : root951.Contains (rootPhase 951) := by
  have hh := CBox.mul_contains_g mid951_contains root1_contains (c:=root951) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root952_contains : root952.Contains (rootPhase 952) := by
  have hh := CBox.mul_contains_g root476_contains root476_contains (c:=root952) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid953_contains : mid953.Contains (rootPhase 952) := root952_contains
lemma root953_contains : root953.Contains (rootPhase 953) := by
  have hh := CBox.mul_contains_g mid953_contains root1_contains (c:=root953) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root954_contains : root954.Contains (rootPhase 954) := by
  have hh := CBox.mul_contains_g root477_contains root477_contains (c:=root954) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid955_contains : mid955.Contains (rootPhase 954) := root954_contains
lemma root955_contains : root955.Contains (rootPhase 955) := by
  have hh := CBox.mul_contains_g mid955_contains root1_contains (c:=root955) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root956_contains : root956.Contains (rootPhase 956) := by
  have hh := CBox.mul_contains_g root478_contains root478_contains (c:=root956) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid957_contains : mid957.Contains (rootPhase 956) := root956_contains
lemma root957_contains : root957.Contains (rootPhase 957) := by
  have hh := CBox.mul_contains_g mid957_contains root1_contains (c:=root957) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root958_contains : root958.Contains (rootPhase 958) := by
  have hh := CBox.mul_contains_g root479_contains root479_contains (c:=root958) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid959_contains : mid959.Contains (rootPhase 958) := root958_contains
lemma root959_contains : root959.Contains (rootPhase 959) := by
  have hh := CBox.mul_contains_g mid959_contains root1_contains (c:=root959) (by decide +kernel)
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
lemma roots29_contains_g_oai (j : Fin 32) : (roots29 j).Contains (rootPhase (928+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root928_contains
  · exact IntegerRoots.root929_contains
  · exact IntegerRoots.root930_contains
  · exact IntegerRoots.root931_contains
  · exact IntegerRoots.root932_contains
  · exact IntegerRoots.root933_contains
  · exact IntegerRoots.root934_contains
  · exact IntegerRoots.root935_contains
  · exact IntegerRoots.root936_contains
  · exact IntegerRoots.root937_contains
  · exact IntegerRoots.root938_contains
  · exact IntegerRoots.root939_contains
  · exact IntegerRoots.root940_contains
  · exact IntegerRoots.root941_contains
  · exact IntegerRoots.root942_contains
  · exact IntegerRoots.root943_contains
  · exact IntegerRoots.root944_contains
  · exact IntegerRoots.root945_contains
  · exact IntegerRoots.root946_contains
  · exact IntegerRoots.root947_contains
  · exact IntegerRoots.root948_contains
  · exact IntegerRoots.root949_contains
  · exact IntegerRoots.root950_contains
  · exact IntegerRoots.root951_contains
  · exact IntegerRoots.root952_contains
  · exact IntegerRoots.root953_contains
  · exact IntegerRoots.root954_contains
  · exact IntegerRoots.root955_contains
  · exact IntegerRoots.root956_contains
  · exact IntegerRoots.root957_contains
  · exact IntegerRoots.root958_contains
  · exact IntegerRoots.root959_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots29_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots29_contains_g_oai
