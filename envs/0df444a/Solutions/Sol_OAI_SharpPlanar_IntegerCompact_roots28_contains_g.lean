-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots28_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:45.30016+00:00
-- url     : https://prove2.me/submissions/4e99d2a4-fd7c-4da6-9025-2a1a631d9081

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
lemma root56_contains : root56.Contains (rootPhase 56) := by
  have hh := CBox.mul_contains_g root28_contains root28_contains (c:=root56) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid57_contains : mid57.Contains (rootPhase 56) := root56_contains
lemma root57_contains : root57.Contains (rootPhase 57) := by
  have hh := CBox.mul_contains_g mid57_contains root1_contains (c:=root57) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root112_contains : root112.Contains (rootPhase 112) := by
  have hh := CBox.mul_contains_g root56_contains root56_contains (c:=root112) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid113_contains : mid113.Contains (rootPhase 112) := root112_contains
lemma root113_contains : root113.Contains (rootPhase 113) := by
  have hh := CBox.mul_contains_g mid113_contains root1_contains (c:=root113) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root114_contains : root114.Contains (rootPhase 114) := by
  have hh := CBox.mul_contains_g root57_contains root57_contains (c:=root114) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid115_contains : mid115.Contains (rootPhase 114) := root114_contains
lemma root115_contains : root115.Contains (rootPhase 115) := by
  have hh := CBox.mul_contains_g mid115_contains root1_contains (c:=root115) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root224_contains : root224.Contains (rootPhase 224) := by
  have hh := CBox.mul_contains_g root112_contains root112_contains (c:=root224) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid225_contains : mid225.Contains (rootPhase 224) := root224_contains
lemma root225_contains : root225.Contains (rootPhase 225) := by
  have hh := CBox.mul_contains_g mid225_contains root1_contains (c:=root225) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root226_contains : root226.Contains (rootPhase 226) := by
  have hh := CBox.mul_contains_g root113_contains root113_contains (c:=root226) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid227_contains : mid227.Contains (rootPhase 226) := root226_contains
lemma root227_contains : root227.Contains (rootPhase 227) := by
  have hh := CBox.mul_contains_g mid227_contains root1_contains (c:=root227) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root228_contains : root228.Contains (rootPhase 228) := by
  have hh := CBox.mul_contains_g root114_contains root114_contains (c:=root228) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid229_contains : mid229.Contains (rootPhase 228) := root228_contains
lemma root229_contains : root229.Contains (rootPhase 229) := by
  have hh := CBox.mul_contains_g mid229_contains root1_contains (c:=root229) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root230_contains : root230.Contains (rootPhase 230) := by
  have hh := CBox.mul_contains_g root115_contains root115_contains (c:=root230) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid231_contains : mid231.Contains (rootPhase 230) := root230_contains
lemma root231_contains : root231.Contains (rootPhase 231) := by
  have hh := CBox.mul_contains_g mid231_contains root1_contains (c:=root231) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root448_contains : root448.Contains (rootPhase 448) := by
  have hh := CBox.mul_contains_g root224_contains root224_contains (c:=root448) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid449_contains : mid449.Contains (rootPhase 448) := root448_contains
lemma root449_contains : root449.Contains (rootPhase 449) := by
  have hh := CBox.mul_contains_g mid449_contains root1_contains (c:=root449) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root450_contains : root450.Contains (rootPhase 450) := by
  have hh := CBox.mul_contains_g root225_contains root225_contains (c:=root450) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid451_contains : mid451.Contains (rootPhase 450) := root450_contains
lemma root451_contains : root451.Contains (rootPhase 451) := by
  have hh := CBox.mul_contains_g mid451_contains root1_contains (c:=root451) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root452_contains : root452.Contains (rootPhase 452) := by
  have hh := CBox.mul_contains_g root226_contains root226_contains (c:=root452) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid453_contains : mid453.Contains (rootPhase 452) := root452_contains
lemma root453_contains : root453.Contains (rootPhase 453) := by
  have hh := CBox.mul_contains_g mid453_contains root1_contains (c:=root453) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root454_contains : root454.Contains (rootPhase 454) := by
  have hh := CBox.mul_contains_g root227_contains root227_contains (c:=root454) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid455_contains : mid455.Contains (rootPhase 454) := root454_contains
lemma root455_contains : root455.Contains (rootPhase 455) := by
  have hh := CBox.mul_contains_g mid455_contains root1_contains (c:=root455) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root456_contains : root456.Contains (rootPhase 456) := by
  have hh := CBox.mul_contains_g root228_contains root228_contains (c:=root456) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid457_contains : mid457.Contains (rootPhase 456) := root456_contains
lemma root457_contains : root457.Contains (rootPhase 457) := by
  have hh := CBox.mul_contains_g mid457_contains root1_contains (c:=root457) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root458_contains : root458.Contains (rootPhase 458) := by
  have hh := CBox.mul_contains_g root229_contains root229_contains (c:=root458) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid459_contains : mid459.Contains (rootPhase 458) := root458_contains
lemma root459_contains : root459.Contains (rootPhase 459) := by
  have hh := CBox.mul_contains_g mid459_contains root1_contains (c:=root459) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root460_contains : root460.Contains (rootPhase 460) := by
  have hh := CBox.mul_contains_g root230_contains root230_contains (c:=root460) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid461_contains : mid461.Contains (rootPhase 460) := root460_contains
lemma root461_contains : root461.Contains (rootPhase 461) := by
  have hh := CBox.mul_contains_g mid461_contains root1_contains (c:=root461) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root462_contains : root462.Contains (rootPhase 462) := by
  have hh := CBox.mul_contains_g root231_contains root231_contains (c:=root462) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid463_contains : mid463.Contains (rootPhase 462) := root462_contains
lemma root463_contains : root463.Contains (rootPhase 463) := by
  have hh := CBox.mul_contains_g mid463_contains root1_contains (c:=root463) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root896_contains : root896.Contains (rootPhase 896) := by
  have hh := CBox.mul_contains_g root448_contains root448_contains (c:=root896) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid897_contains : mid897.Contains (rootPhase 896) := root896_contains
lemma root897_contains : root897.Contains (rootPhase 897) := by
  have hh := CBox.mul_contains_g mid897_contains root1_contains (c:=root897) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root898_contains : root898.Contains (rootPhase 898) := by
  have hh := CBox.mul_contains_g root449_contains root449_contains (c:=root898) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid899_contains : mid899.Contains (rootPhase 898) := root898_contains
lemma root899_contains : root899.Contains (rootPhase 899) := by
  have hh := CBox.mul_contains_g mid899_contains root1_contains (c:=root899) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root900_contains : root900.Contains (rootPhase 900) := by
  have hh := CBox.mul_contains_g root450_contains root450_contains (c:=root900) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid901_contains : mid901.Contains (rootPhase 900) := root900_contains
lemma root901_contains : root901.Contains (rootPhase 901) := by
  have hh := CBox.mul_contains_g mid901_contains root1_contains (c:=root901) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root902_contains : root902.Contains (rootPhase 902) := by
  have hh := CBox.mul_contains_g root451_contains root451_contains (c:=root902) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid903_contains : mid903.Contains (rootPhase 902) := root902_contains
lemma root903_contains : root903.Contains (rootPhase 903) := by
  have hh := CBox.mul_contains_g mid903_contains root1_contains (c:=root903) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root904_contains : root904.Contains (rootPhase 904) := by
  have hh := CBox.mul_contains_g root452_contains root452_contains (c:=root904) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid905_contains : mid905.Contains (rootPhase 904) := root904_contains
lemma root905_contains : root905.Contains (rootPhase 905) := by
  have hh := CBox.mul_contains_g mid905_contains root1_contains (c:=root905) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root906_contains : root906.Contains (rootPhase 906) := by
  have hh := CBox.mul_contains_g root453_contains root453_contains (c:=root906) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid907_contains : mid907.Contains (rootPhase 906) := root906_contains
lemma root907_contains : root907.Contains (rootPhase 907) := by
  have hh := CBox.mul_contains_g mid907_contains root1_contains (c:=root907) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root908_contains : root908.Contains (rootPhase 908) := by
  have hh := CBox.mul_contains_g root454_contains root454_contains (c:=root908) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid909_contains : mid909.Contains (rootPhase 908) := root908_contains
lemma root909_contains : root909.Contains (rootPhase 909) := by
  have hh := CBox.mul_contains_g mid909_contains root1_contains (c:=root909) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root910_contains : root910.Contains (rootPhase 910) := by
  have hh := CBox.mul_contains_g root455_contains root455_contains (c:=root910) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid911_contains : mid911.Contains (rootPhase 910) := root910_contains
lemma root911_contains : root911.Contains (rootPhase 911) := by
  have hh := CBox.mul_contains_g mid911_contains root1_contains (c:=root911) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root912_contains : root912.Contains (rootPhase 912) := by
  have hh := CBox.mul_contains_g root456_contains root456_contains (c:=root912) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid913_contains : mid913.Contains (rootPhase 912) := root912_contains
lemma root913_contains : root913.Contains (rootPhase 913) := by
  have hh := CBox.mul_contains_g mid913_contains root1_contains (c:=root913) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root914_contains : root914.Contains (rootPhase 914) := by
  have hh := CBox.mul_contains_g root457_contains root457_contains (c:=root914) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid915_contains : mid915.Contains (rootPhase 914) := root914_contains
lemma root915_contains : root915.Contains (rootPhase 915) := by
  have hh := CBox.mul_contains_g mid915_contains root1_contains (c:=root915) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root916_contains : root916.Contains (rootPhase 916) := by
  have hh := CBox.mul_contains_g root458_contains root458_contains (c:=root916) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid917_contains : mid917.Contains (rootPhase 916) := root916_contains
lemma root917_contains : root917.Contains (rootPhase 917) := by
  have hh := CBox.mul_contains_g mid917_contains root1_contains (c:=root917) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root918_contains : root918.Contains (rootPhase 918) := by
  have hh := CBox.mul_contains_g root459_contains root459_contains (c:=root918) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid919_contains : mid919.Contains (rootPhase 918) := root918_contains
lemma root919_contains : root919.Contains (rootPhase 919) := by
  have hh := CBox.mul_contains_g mid919_contains root1_contains (c:=root919) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root920_contains : root920.Contains (rootPhase 920) := by
  have hh := CBox.mul_contains_g root460_contains root460_contains (c:=root920) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid921_contains : mid921.Contains (rootPhase 920) := root920_contains
lemma root921_contains : root921.Contains (rootPhase 921) := by
  have hh := CBox.mul_contains_g mid921_contains root1_contains (c:=root921) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root922_contains : root922.Contains (rootPhase 922) := by
  have hh := CBox.mul_contains_g root461_contains root461_contains (c:=root922) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid923_contains : mid923.Contains (rootPhase 922) := root922_contains
lemma root923_contains : root923.Contains (rootPhase 923) := by
  have hh := CBox.mul_contains_g mid923_contains root1_contains (c:=root923) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root924_contains : root924.Contains (rootPhase 924) := by
  have hh := CBox.mul_contains_g root462_contains root462_contains (c:=root924) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid925_contains : mid925.Contains (rootPhase 924) := root924_contains
lemma root925_contains : root925.Contains (rootPhase 925) := by
  have hh := CBox.mul_contains_g mid925_contains root1_contains (c:=root925) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root926_contains : root926.Contains (rootPhase 926) := by
  have hh := CBox.mul_contains_g root463_contains root463_contains (c:=root926) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid927_contains : mid927.Contains (rootPhase 926) := root926_contains
lemma root927_contains : root927.Contains (rootPhase 927) := by
  have hh := CBox.mul_contains_g mid927_contains root1_contains (c:=root927) (by decide +kernel)
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
lemma roots28_contains_g_oai (j : Fin 32) : (roots28 j).Contains (rootPhase (896+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root896_contains
  · exact IntegerRoots.root897_contains
  · exact IntegerRoots.root898_contains
  · exact IntegerRoots.root899_contains
  · exact IntegerRoots.root900_contains
  · exact IntegerRoots.root901_contains
  · exact IntegerRoots.root902_contains
  · exact IntegerRoots.root903_contains
  · exact IntegerRoots.root904_contains
  · exact IntegerRoots.root905_contains
  · exact IntegerRoots.root906_contains
  · exact IntegerRoots.root907_contains
  · exact IntegerRoots.root908_contains
  · exact IntegerRoots.root909_contains
  · exact IntegerRoots.root910_contains
  · exact IntegerRoots.root911_contains
  · exact IntegerRoots.root912_contains
  · exact IntegerRoots.root913_contains
  · exact IntegerRoots.root914_contains
  · exact IntegerRoots.root915_contains
  · exact IntegerRoots.root916_contains
  · exact IntegerRoots.root917_contains
  · exact IntegerRoots.root918_contains
  · exact IntegerRoots.root919_contains
  · exact IntegerRoots.root920_contains
  · exact IntegerRoots.root921_contains
  · exact IntegerRoots.root922_contains
  · exact IntegerRoots.root923_contains
  · exact IntegerRoots.root924_contains
  · exact IntegerRoots.root925_contains
  · exact IntegerRoots.root926_contains
  · exact IntegerRoots.root927_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots28_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots28_contains_g_oai
