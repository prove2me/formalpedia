-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots20_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:30:40.219168+00:00
-- url     : https://prove2.me/submissions/d5c37275-71af-474f-9348-8675af663095

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
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains_g mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains_g root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root20_contains : root20.Contains (rootPhase 20) := by
  have hh := CBox.mul_contains_g root10_contains root10_contains (c:=root20) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root40_contains : root40.Contains (rootPhase 40) := by
  have hh := CBox.mul_contains_g root20_contains root20_contains (c:=root40) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid41_contains : mid41.Contains (rootPhase 40) := root40_contains
lemma root41_contains : root41.Contains (rootPhase 41) := by
  have hh := CBox.mul_contains_g mid41_contains root1_contains (c:=root41) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root80_contains : root80.Contains (rootPhase 80) := by
  have hh := CBox.mul_contains_g root40_contains root40_contains (c:=root80) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid81_contains : mid81.Contains (rootPhase 80) := root80_contains
lemma root81_contains : root81.Contains (rootPhase 81) := by
  have hh := CBox.mul_contains_g mid81_contains root1_contains (c:=root81) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root82_contains : root82.Contains (rootPhase 82) := by
  have hh := CBox.mul_contains_g root41_contains root41_contains (c:=root82) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid83_contains : mid83.Contains (rootPhase 82) := root82_contains
lemma root83_contains : root83.Contains (rootPhase 83) := by
  have hh := CBox.mul_contains_g mid83_contains root1_contains (c:=root83) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root160_contains : root160.Contains (rootPhase 160) := by
  have hh := CBox.mul_contains_g root80_contains root80_contains (c:=root160) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid161_contains : mid161.Contains (rootPhase 160) := root160_contains
lemma root161_contains : root161.Contains (rootPhase 161) := by
  have hh := CBox.mul_contains_g mid161_contains root1_contains (c:=root161) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root162_contains : root162.Contains (rootPhase 162) := by
  have hh := CBox.mul_contains_g root81_contains root81_contains (c:=root162) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid163_contains : mid163.Contains (rootPhase 162) := root162_contains
lemma root163_contains : root163.Contains (rootPhase 163) := by
  have hh := CBox.mul_contains_g mid163_contains root1_contains (c:=root163) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root164_contains : root164.Contains (rootPhase 164) := by
  have hh := CBox.mul_contains_g root82_contains root82_contains (c:=root164) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid165_contains : mid165.Contains (rootPhase 164) := root164_contains
lemma root165_contains : root165.Contains (rootPhase 165) := by
  have hh := CBox.mul_contains_g mid165_contains root1_contains (c:=root165) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root166_contains : root166.Contains (rootPhase 166) := by
  have hh := CBox.mul_contains_g root83_contains root83_contains (c:=root166) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid167_contains : mid167.Contains (rootPhase 166) := root166_contains
lemma root167_contains : root167.Contains (rootPhase 167) := by
  have hh := CBox.mul_contains_g mid167_contains root1_contains (c:=root167) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root320_contains : root320.Contains (rootPhase 320) := by
  have hh := CBox.mul_contains_g root160_contains root160_contains (c:=root320) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid321_contains : mid321.Contains (rootPhase 320) := root320_contains
lemma root321_contains : root321.Contains (rootPhase 321) := by
  have hh := CBox.mul_contains_g mid321_contains root1_contains (c:=root321) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root322_contains : root322.Contains (rootPhase 322) := by
  have hh := CBox.mul_contains_g root161_contains root161_contains (c:=root322) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid323_contains : mid323.Contains (rootPhase 322) := root322_contains
lemma root323_contains : root323.Contains (rootPhase 323) := by
  have hh := CBox.mul_contains_g mid323_contains root1_contains (c:=root323) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root324_contains : root324.Contains (rootPhase 324) := by
  have hh := CBox.mul_contains_g root162_contains root162_contains (c:=root324) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid325_contains : mid325.Contains (rootPhase 324) := root324_contains
lemma root325_contains : root325.Contains (rootPhase 325) := by
  have hh := CBox.mul_contains_g mid325_contains root1_contains (c:=root325) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root326_contains : root326.Contains (rootPhase 326) := by
  have hh := CBox.mul_contains_g root163_contains root163_contains (c:=root326) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid327_contains : mid327.Contains (rootPhase 326) := root326_contains
lemma root327_contains : root327.Contains (rootPhase 327) := by
  have hh := CBox.mul_contains_g mid327_contains root1_contains (c:=root327) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root328_contains : root328.Contains (rootPhase 328) := by
  have hh := CBox.mul_contains_g root164_contains root164_contains (c:=root328) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid329_contains : mid329.Contains (rootPhase 328) := root328_contains
lemma root329_contains : root329.Contains (rootPhase 329) := by
  have hh := CBox.mul_contains_g mid329_contains root1_contains (c:=root329) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root330_contains : root330.Contains (rootPhase 330) := by
  have hh := CBox.mul_contains_g root165_contains root165_contains (c:=root330) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid331_contains : mid331.Contains (rootPhase 330) := root330_contains
lemma root331_contains : root331.Contains (rootPhase 331) := by
  have hh := CBox.mul_contains_g mid331_contains root1_contains (c:=root331) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root332_contains : root332.Contains (rootPhase 332) := by
  have hh := CBox.mul_contains_g root166_contains root166_contains (c:=root332) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid333_contains : mid333.Contains (rootPhase 332) := root332_contains
lemma root333_contains : root333.Contains (rootPhase 333) := by
  have hh := CBox.mul_contains_g mid333_contains root1_contains (c:=root333) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root334_contains : root334.Contains (rootPhase 334) := by
  have hh := CBox.mul_contains_g root167_contains root167_contains (c:=root334) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid335_contains : mid335.Contains (rootPhase 334) := root334_contains
lemma root335_contains : root335.Contains (rootPhase 335) := by
  have hh := CBox.mul_contains_g mid335_contains root1_contains (c:=root335) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root640_contains : root640.Contains (rootPhase 640) := by
  have hh := CBox.mul_contains_g root320_contains root320_contains (c:=root640) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid641_contains : mid641.Contains (rootPhase 640) := root640_contains
lemma root641_contains : root641.Contains (rootPhase 641) := by
  have hh := CBox.mul_contains_g mid641_contains root1_contains (c:=root641) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root642_contains : root642.Contains (rootPhase 642) := by
  have hh := CBox.mul_contains_g root321_contains root321_contains (c:=root642) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid643_contains : mid643.Contains (rootPhase 642) := root642_contains
lemma root643_contains : root643.Contains (rootPhase 643) := by
  have hh := CBox.mul_contains_g mid643_contains root1_contains (c:=root643) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root644_contains : root644.Contains (rootPhase 644) := by
  have hh := CBox.mul_contains_g root322_contains root322_contains (c:=root644) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid645_contains : mid645.Contains (rootPhase 644) := root644_contains
lemma root645_contains : root645.Contains (rootPhase 645) := by
  have hh := CBox.mul_contains_g mid645_contains root1_contains (c:=root645) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root646_contains : root646.Contains (rootPhase 646) := by
  have hh := CBox.mul_contains_g root323_contains root323_contains (c:=root646) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid647_contains : mid647.Contains (rootPhase 646) := root646_contains
lemma root647_contains : root647.Contains (rootPhase 647) := by
  have hh := CBox.mul_contains_g mid647_contains root1_contains (c:=root647) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root648_contains : root648.Contains (rootPhase 648) := by
  have hh := CBox.mul_contains_g root324_contains root324_contains (c:=root648) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid649_contains : mid649.Contains (rootPhase 648) := root648_contains
lemma root649_contains : root649.Contains (rootPhase 649) := by
  have hh := CBox.mul_contains_g mid649_contains root1_contains (c:=root649) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root650_contains : root650.Contains (rootPhase 650) := by
  have hh := CBox.mul_contains_g root325_contains root325_contains (c:=root650) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid651_contains : mid651.Contains (rootPhase 650) := root650_contains
lemma root651_contains : root651.Contains (rootPhase 651) := by
  have hh := CBox.mul_contains_g mid651_contains root1_contains (c:=root651) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root652_contains : root652.Contains (rootPhase 652) := by
  have hh := CBox.mul_contains_g root326_contains root326_contains (c:=root652) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid653_contains : mid653.Contains (rootPhase 652) := root652_contains
lemma root653_contains : root653.Contains (rootPhase 653) := by
  have hh := CBox.mul_contains_g mid653_contains root1_contains (c:=root653) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root654_contains : root654.Contains (rootPhase 654) := by
  have hh := CBox.mul_contains_g root327_contains root327_contains (c:=root654) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid655_contains : mid655.Contains (rootPhase 654) := root654_contains
lemma root655_contains : root655.Contains (rootPhase 655) := by
  have hh := CBox.mul_contains_g mid655_contains root1_contains (c:=root655) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root656_contains : root656.Contains (rootPhase 656) := by
  have hh := CBox.mul_contains_g root328_contains root328_contains (c:=root656) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid657_contains : mid657.Contains (rootPhase 656) := root656_contains
lemma root657_contains : root657.Contains (rootPhase 657) := by
  have hh := CBox.mul_contains_g mid657_contains root1_contains (c:=root657) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root658_contains : root658.Contains (rootPhase 658) := by
  have hh := CBox.mul_contains_g root329_contains root329_contains (c:=root658) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid659_contains : mid659.Contains (rootPhase 658) := root658_contains
lemma root659_contains : root659.Contains (rootPhase 659) := by
  have hh := CBox.mul_contains_g mid659_contains root1_contains (c:=root659) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root660_contains : root660.Contains (rootPhase 660) := by
  have hh := CBox.mul_contains_g root330_contains root330_contains (c:=root660) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid661_contains : mid661.Contains (rootPhase 660) := root660_contains
lemma root661_contains : root661.Contains (rootPhase 661) := by
  have hh := CBox.mul_contains_g mid661_contains root1_contains (c:=root661) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root662_contains : root662.Contains (rootPhase 662) := by
  have hh := CBox.mul_contains_g root331_contains root331_contains (c:=root662) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid663_contains : mid663.Contains (rootPhase 662) := root662_contains
lemma root663_contains : root663.Contains (rootPhase 663) := by
  have hh := CBox.mul_contains_g mid663_contains root1_contains (c:=root663) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root664_contains : root664.Contains (rootPhase 664) := by
  have hh := CBox.mul_contains_g root332_contains root332_contains (c:=root664) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid665_contains : mid665.Contains (rootPhase 664) := root664_contains
lemma root665_contains : root665.Contains (rootPhase 665) := by
  have hh := CBox.mul_contains_g mid665_contains root1_contains (c:=root665) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root666_contains : root666.Contains (rootPhase 666) := by
  have hh := CBox.mul_contains_g root333_contains root333_contains (c:=root666) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid667_contains : mid667.Contains (rootPhase 666) := root666_contains
lemma root667_contains : root667.Contains (rootPhase 667) := by
  have hh := CBox.mul_contains_g mid667_contains root1_contains (c:=root667) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root668_contains : root668.Contains (rootPhase 668) := by
  have hh := CBox.mul_contains_g root334_contains root334_contains (c:=root668) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid669_contains : mid669.Contains (rootPhase 668) := root668_contains
lemma root669_contains : root669.Contains (rootPhase 669) := by
  have hh := CBox.mul_contains_g mid669_contains root1_contains (c:=root669) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root670_contains : root670.Contains (rootPhase 670) := by
  have hh := CBox.mul_contains_g root335_contains root335_contains (c:=root670) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid671_contains : mid671.Contains (rootPhase 670) := root670_contains
lemma root671_contains : root671.Contains (rootPhase 671) := by
  have hh := CBox.mul_contains_g mid671_contains root1_contains (c:=root671) (by decide +kernel)
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
lemma roots20_contains_g_oai (j : Fin 32) : (roots20 j).Contains (rootPhase (640+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root640_contains
  · exact IntegerRoots.root641_contains
  · exact IntegerRoots.root642_contains
  · exact IntegerRoots.root643_contains
  · exact IntegerRoots.root644_contains
  · exact IntegerRoots.root645_contains
  · exact IntegerRoots.root646_contains
  · exact IntegerRoots.root647_contains
  · exact IntegerRoots.root648_contains
  · exact IntegerRoots.root649_contains
  · exact IntegerRoots.root650_contains
  · exact IntegerRoots.root651_contains
  · exact IntegerRoots.root652_contains
  · exact IntegerRoots.root653_contains
  · exact IntegerRoots.root654_contains
  · exact IntegerRoots.root655_contains
  · exact IntegerRoots.root656_contains
  · exact IntegerRoots.root657_contains
  · exact IntegerRoots.root658_contains
  · exact IntegerRoots.root659_contains
  · exact IntegerRoots.root660_contains
  · exact IntegerRoots.root661_contains
  · exact IntegerRoots.root662_contains
  · exact IntegerRoots.root663_contains
  · exact IntegerRoots.root664_contains
  · exact IntegerRoots.root665_contains
  · exact IntegerRoots.root666_contains
  · exact IntegerRoots.root667_contains
  · exact IntegerRoots.root668_contains
  · exact IntegerRoots.root669_contains
  · exact IntegerRoots.root670_contains
  · exact IntegerRoots.root671_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots20_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots20_contains_g_oai
