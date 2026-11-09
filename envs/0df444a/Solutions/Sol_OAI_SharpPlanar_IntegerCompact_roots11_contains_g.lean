-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots11_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:07:02.219345+00:00
-- url     : https://prove2.me/submissions/7da579ed-f43e-4bd4-b603-ca16c1fb4c9d

import Mathlib
import Definitions.Def_OAIQ098G023
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
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains_g mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains_g root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid11_contains : mid11.Contains (rootPhase 10) := root10_contains
lemma root11_contains : root11.Contains (rootPhase 11) := by
  have hh := CBox.mul_contains_g mid11_contains root1_contains (c:=root11) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root22_contains : root22.Contains (rootPhase 22) := by
  have hh := CBox.mul_contains_g root11_contains root11_contains (c:=root22) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid23_contains : mid23.Contains (rootPhase 22) := root22_contains
lemma root23_contains : root23.Contains (rootPhase 23) := by
  have hh := CBox.mul_contains_g mid23_contains root1_contains (c:=root23) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root44_contains : root44.Contains (rootPhase 44) := by
  have hh := CBox.mul_contains_g root22_contains root22_contains (c:=root44) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid45_contains : mid45.Contains (rootPhase 44) := root44_contains
lemma root45_contains : root45.Contains (rootPhase 45) := by
  have hh := CBox.mul_contains_g mid45_contains root1_contains (c:=root45) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root46_contains : root46.Contains (rootPhase 46) := by
  have hh := CBox.mul_contains_g root23_contains root23_contains (c:=root46) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid47_contains : mid47.Contains (rootPhase 46) := root46_contains
lemma root47_contains : root47.Contains (rootPhase 47) := by
  have hh := CBox.mul_contains_g mid47_contains root1_contains (c:=root47) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root88_contains : root88.Contains (rootPhase 88) := by
  have hh := CBox.mul_contains_g root44_contains root44_contains (c:=root88) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid89_contains : mid89.Contains (rootPhase 88) := root88_contains
lemma root89_contains : root89.Contains (rootPhase 89) := by
  have hh := CBox.mul_contains_g mid89_contains root1_contains (c:=root89) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root90_contains : root90.Contains (rootPhase 90) := by
  have hh := CBox.mul_contains_g root45_contains root45_contains (c:=root90) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid91_contains : mid91.Contains (rootPhase 90) := root90_contains
lemma root91_contains : root91.Contains (rootPhase 91) := by
  have hh := CBox.mul_contains_g mid91_contains root1_contains (c:=root91) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root92_contains : root92.Contains (rootPhase 92) := by
  have hh := CBox.mul_contains_g root46_contains root46_contains (c:=root92) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid93_contains : mid93.Contains (rootPhase 92) := root92_contains
lemma root93_contains : root93.Contains (rootPhase 93) := by
  have hh := CBox.mul_contains_g mid93_contains root1_contains (c:=root93) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root94_contains : root94.Contains (rootPhase 94) := by
  have hh := CBox.mul_contains_g root47_contains root47_contains (c:=root94) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid95_contains : mid95.Contains (rootPhase 94) := root94_contains
lemma root95_contains : root95.Contains (rootPhase 95) := by
  have hh := CBox.mul_contains_g mid95_contains root1_contains (c:=root95) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root176_contains : root176.Contains (rootPhase 176) := by
  have hh := CBox.mul_contains_g root88_contains root88_contains (c:=root176) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid177_contains : mid177.Contains (rootPhase 176) := root176_contains
lemma root177_contains : root177.Contains (rootPhase 177) := by
  have hh := CBox.mul_contains_g mid177_contains root1_contains (c:=root177) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root178_contains : root178.Contains (rootPhase 178) := by
  have hh := CBox.mul_contains_g root89_contains root89_contains (c:=root178) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid179_contains : mid179.Contains (rootPhase 178) := root178_contains
lemma root179_contains : root179.Contains (rootPhase 179) := by
  have hh := CBox.mul_contains_g mid179_contains root1_contains (c:=root179) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root180_contains : root180.Contains (rootPhase 180) := by
  have hh := CBox.mul_contains_g root90_contains root90_contains (c:=root180) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid181_contains : mid181.Contains (rootPhase 180) := root180_contains
lemma root181_contains : root181.Contains (rootPhase 181) := by
  have hh := CBox.mul_contains_g mid181_contains root1_contains (c:=root181) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root182_contains : root182.Contains (rootPhase 182) := by
  have hh := CBox.mul_contains_g root91_contains root91_contains (c:=root182) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid183_contains : mid183.Contains (rootPhase 182) := root182_contains
lemma root183_contains : root183.Contains (rootPhase 183) := by
  have hh := CBox.mul_contains_g mid183_contains root1_contains (c:=root183) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root184_contains : root184.Contains (rootPhase 184) := by
  have hh := CBox.mul_contains_g root92_contains root92_contains (c:=root184) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid185_contains : mid185.Contains (rootPhase 184) := root184_contains
lemma root185_contains : root185.Contains (rootPhase 185) := by
  have hh := CBox.mul_contains_g mid185_contains root1_contains (c:=root185) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root186_contains : root186.Contains (rootPhase 186) := by
  have hh := CBox.mul_contains_g root93_contains root93_contains (c:=root186) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid187_contains : mid187.Contains (rootPhase 186) := root186_contains
lemma root187_contains : root187.Contains (rootPhase 187) := by
  have hh := CBox.mul_contains_g mid187_contains root1_contains (c:=root187) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root188_contains : root188.Contains (rootPhase 188) := by
  have hh := CBox.mul_contains_g root94_contains root94_contains (c:=root188) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid189_contains : mid189.Contains (rootPhase 188) := root188_contains
lemma root189_contains : root189.Contains (rootPhase 189) := by
  have hh := CBox.mul_contains_g mid189_contains root1_contains (c:=root189) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root190_contains : root190.Contains (rootPhase 190) := by
  have hh := CBox.mul_contains_g root95_contains root95_contains (c:=root190) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid191_contains : mid191.Contains (rootPhase 190) := root190_contains
lemma root191_contains : root191.Contains (rootPhase 191) := by
  have hh := CBox.mul_contains_g mid191_contains root1_contains (c:=root191) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root352_contains : root352.Contains (rootPhase 352) := by
  have hh := CBox.mul_contains_g root176_contains root176_contains (c:=root352) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid353_contains : mid353.Contains (rootPhase 352) := root352_contains
lemma root353_contains : root353.Contains (rootPhase 353) := by
  have hh := CBox.mul_contains_g mid353_contains root1_contains (c:=root353) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root354_contains : root354.Contains (rootPhase 354) := by
  have hh := CBox.mul_contains_g root177_contains root177_contains (c:=root354) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid355_contains : mid355.Contains (rootPhase 354) := root354_contains
lemma root355_contains : root355.Contains (rootPhase 355) := by
  have hh := CBox.mul_contains_g mid355_contains root1_contains (c:=root355) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root356_contains : root356.Contains (rootPhase 356) := by
  have hh := CBox.mul_contains_g root178_contains root178_contains (c:=root356) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid357_contains : mid357.Contains (rootPhase 356) := root356_contains
lemma root357_contains : root357.Contains (rootPhase 357) := by
  have hh := CBox.mul_contains_g mid357_contains root1_contains (c:=root357) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root358_contains : root358.Contains (rootPhase 358) := by
  have hh := CBox.mul_contains_g root179_contains root179_contains (c:=root358) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid359_contains : mid359.Contains (rootPhase 358) := root358_contains
lemma root359_contains : root359.Contains (rootPhase 359) := by
  have hh := CBox.mul_contains_g mid359_contains root1_contains (c:=root359) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root360_contains : root360.Contains (rootPhase 360) := by
  have hh := CBox.mul_contains_g root180_contains root180_contains (c:=root360) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid361_contains : mid361.Contains (rootPhase 360) := root360_contains
lemma root361_contains : root361.Contains (rootPhase 361) := by
  have hh := CBox.mul_contains_g mid361_contains root1_contains (c:=root361) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root362_contains : root362.Contains (rootPhase 362) := by
  have hh := CBox.mul_contains_g root181_contains root181_contains (c:=root362) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid363_contains : mid363.Contains (rootPhase 362) := root362_contains
lemma root363_contains : root363.Contains (rootPhase 363) := by
  have hh := CBox.mul_contains_g mid363_contains root1_contains (c:=root363) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root364_contains : root364.Contains (rootPhase 364) := by
  have hh := CBox.mul_contains_g root182_contains root182_contains (c:=root364) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid365_contains : mid365.Contains (rootPhase 364) := root364_contains
lemma root365_contains : root365.Contains (rootPhase 365) := by
  have hh := CBox.mul_contains_g mid365_contains root1_contains (c:=root365) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root366_contains : root366.Contains (rootPhase 366) := by
  have hh := CBox.mul_contains_g root183_contains root183_contains (c:=root366) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid367_contains : mid367.Contains (rootPhase 366) := root366_contains
lemma root367_contains : root367.Contains (rootPhase 367) := by
  have hh := CBox.mul_contains_g mid367_contains root1_contains (c:=root367) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root368_contains : root368.Contains (rootPhase 368) := by
  have hh := CBox.mul_contains_g root184_contains root184_contains (c:=root368) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid369_contains : mid369.Contains (rootPhase 368) := root368_contains
lemma root369_contains : root369.Contains (rootPhase 369) := by
  have hh := CBox.mul_contains_g mid369_contains root1_contains (c:=root369) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root370_contains : root370.Contains (rootPhase 370) := by
  have hh := CBox.mul_contains_g root185_contains root185_contains (c:=root370) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid371_contains : mid371.Contains (rootPhase 370) := root370_contains
lemma root371_contains : root371.Contains (rootPhase 371) := by
  have hh := CBox.mul_contains_g mid371_contains root1_contains (c:=root371) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root372_contains : root372.Contains (rootPhase 372) := by
  have hh := CBox.mul_contains_g root186_contains root186_contains (c:=root372) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid373_contains : mid373.Contains (rootPhase 372) := root372_contains
lemma root373_contains : root373.Contains (rootPhase 373) := by
  have hh := CBox.mul_contains_g mid373_contains root1_contains (c:=root373) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root374_contains : root374.Contains (rootPhase 374) := by
  have hh := CBox.mul_contains_g root187_contains root187_contains (c:=root374) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid375_contains : mid375.Contains (rootPhase 374) := root374_contains
lemma root375_contains : root375.Contains (rootPhase 375) := by
  have hh := CBox.mul_contains_g mid375_contains root1_contains (c:=root375) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root376_contains : root376.Contains (rootPhase 376) := by
  have hh := CBox.mul_contains_g root188_contains root188_contains (c:=root376) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid377_contains : mid377.Contains (rootPhase 376) := root376_contains
lemma root377_contains : root377.Contains (rootPhase 377) := by
  have hh := CBox.mul_contains_g mid377_contains root1_contains (c:=root377) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root378_contains : root378.Contains (rootPhase 378) := by
  have hh := CBox.mul_contains_g root189_contains root189_contains (c:=root378) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid379_contains : mid379.Contains (rootPhase 378) := root378_contains
lemma root379_contains : root379.Contains (rootPhase 379) := by
  have hh := CBox.mul_contains_g mid379_contains root1_contains (c:=root379) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root380_contains : root380.Contains (rootPhase 380) := by
  have hh := CBox.mul_contains_g root190_contains root190_contains (c:=root380) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid381_contains : mid381.Contains (rootPhase 380) := root380_contains
lemma root381_contains : root381.Contains (rootPhase 381) := by
  have hh := CBox.mul_contains_g mid381_contains root1_contains (c:=root381) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root382_contains : root382.Contains (rootPhase 382) := by
  have hh := CBox.mul_contains_g root191_contains root191_contains (c:=root382) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid383_contains : mid383.Contains (rootPhase 382) := root382_contains
lemma root383_contains : root383.Contains (rootPhase 383) := by
  have hh := CBox.mul_contains_g mid383_contains root1_contains (c:=root383) (by decide +kernel)
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
lemma roots11_contains_g_oai (j : Fin 32) : (roots11 j).Contains (rootPhase (352+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root352_contains
  · exact IntegerRoots.root353_contains
  · exact IntegerRoots.root354_contains
  · exact IntegerRoots.root355_contains
  · exact IntegerRoots.root356_contains
  · exact IntegerRoots.root357_contains
  · exact IntegerRoots.root358_contains
  · exact IntegerRoots.root359_contains
  · exact IntegerRoots.root360_contains
  · exact IntegerRoots.root361_contains
  · exact IntegerRoots.root362_contains
  · exact IntegerRoots.root363_contains
  · exact IntegerRoots.root364_contains
  · exact IntegerRoots.root365_contains
  · exact IntegerRoots.root366_contains
  · exact IntegerRoots.root367_contains
  · exact IntegerRoots.root368_contains
  · exact IntegerRoots.root369_contains
  · exact IntegerRoots.root370_contains
  · exact IntegerRoots.root371_contains
  · exact IntegerRoots.root372_contains
  · exact IntegerRoots.root373_contains
  · exact IntegerRoots.root374_contains
  · exact IntegerRoots.root375_contains
  · exact IntegerRoots.root376_contains
  · exact IntegerRoots.root377_contains
  · exact IntegerRoots.root378_contains
  · exact IntegerRoots.root379_contains
  · exact IntegerRoots.root380_contains
  · exact IntegerRoots.root381_contains
  · exact IntegerRoots.root382_contains
  · exact IntegerRoots.root383_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots11_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots11_contains_g_oai
