-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.roots25_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:31:14.892856+00:00
-- url     : https://prove2.me/submissions/33e8dfa7-2c7f-4590-82ab-e5ede9a8544e

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
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains_g root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains_g root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid25_contains : mid25.Contains (rootPhase 24) := root24_contains
lemma root25_contains : root25.Contains (rootPhase 25) := by
  have hh := CBox.mul_contains_g mid25_contains root1_contains (c:=root25) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root50_contains : root50.Contains (rootPhase 50) := by
  have hh := CBox.mul_contains_g root25_contains root25_contains (c:=root50) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid51_contains : mid51.Contains (rootPhase 50) := root50_contains
lemma root51_contains : root51.Contains (rootPhase 51) := by
  have hh := CBox.mul_contains_g mid51_contains root1_contains (c:=root51) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root100_contains : root100.Contains (rootPhase 100) := by
  have hh := CBox.mul_contains_g root50_contains root50_contains (c:=root100) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid101_contains : mid101.Contains (rootPhase 100) := root100_contains
lemma root101_contains : root101.Contains (rootPhase 101) := by
  have hh := CBox.mul_contains_g mid101_contains root1_contains (c:=root101) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root102_contains : root102.Contains (rootPhase 102) := by
  have hh := CBox.mul_contains_g root51_contains root51_contains (c:=root102) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid103_contains : mid103.Contains (rootPhase 102) := root102_contains
lemma root103_contains : root103.Contains (rootPhase 103) := by
  have hh := CBox.mul_contains_g mid103_contains root1_contains (c:=root103) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root200_contains : root200.Contains (rootPhase 200) := by
  have hh := CBox.mul_contains_g root100_contains root100_contains (c:=root200) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid201_contains : mid201.Contains (rootPhase 200) := root200_contains
lemma root201_contains : root201.Contains (rootPhase 201) := by
  have hh := CBox.mul_contains_g mid201_contains root1_contains (c:=root201) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root202_contains : root202.Contains (rootPhase 202) := by
  have hh := CBox.mul_contains_g root101_contains root101_contains (c:=root202) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid203_contains : mid203.Contains (rootPhase 202) := root202_contains
lemma root203_contains : root203.Contains (rootPhase 203) := by
  have hh := CBox.mul_contains_g mid203_contains root1_contains (c:=root203) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root204_contains : root204.Contains (rootPhase 204) := by
  have hh := CBox.mul_contains_g root102_contains root102_contains (c:=root204) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid205_contains : mid205.Contains (rootPhase 204) := root204_contains
lemma root205_contains : root205.Contains (rootPhase 205) := by
  have hh := CBox.mul_contains_g mid205_contains root1_contains (c:=root205) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root206_contains : root206.Contains (rootPhase 206) := by
  have hh := CBox.mul_contains_g root103_contains root103_contains (c:=root206) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid207_contains : mid207.Contains (rootPhase 206) := root206_contains
lemma root207_contains : root207.Contains (rootPhase 207) := by
  have hh := CBox.mul_contains_g mid207_contains root1_contains (c:=root207) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root400_contains : root400.Contains (rootPhase 400) := by
  have hh := CBox.mul_contains_g root200_contains root200_contains (c:=root400) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid401_contains : mid401.Contains (rootPhase 400) := root400_contains
lemma root401_contains : root401.Contains (rootPhase 401) := by
  have hh := CBox.mul_contains_g mid401_contains root1_contains (c:=root401) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root402_contains : root402.Contains (rootPhase 402) := by
  have hh := CBox.mul_contains_g root201_contains root201_contains (c:=root402) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid403_contains : mid403.Contains (rootPhase 402) := root402_contains
lemma root403_contains : root403.Contains (rootPhase 403) := by
  have hh := CBox.mul_contains_g mid403_contains root1_contains (c:=root403) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root404_contains : root404.Contains (rootPhase 404) := by
  have hh := CBox.mul_contains_g root202_contains root202_contains (c:=root404) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid405_contains : mid405.Contains (rootPhase 404) := root404_contains
lemma root405_contains : root405.Contains (rootPhase 405) := by
  have hh := CBox.mul_contains_g mid405_contains root1_contains (c:=root405) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root406_contains : root406.Contains (rootPhase 406) := by
  have hh := CBox.mul_contains_g root203_contains root203_contains (c:=root406) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid407_contains : mid407.Contains (rootPhase 406) := root406_contains
lemma root407_contains : root407.Contains (rootPhase 407) := by
  have hh := CBox.mul_contains_g mid407_contains root1_contains (c:=root407) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root408_contains : root408.Contains (rootPhase 408) := by
  have hh := CBox.mul_contains_g root204_contains root204_contains (c:=root408) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid409_contains : mid409.Contains (rootPhase 408) := root408_contains
lemma root409_contains : root409.Contains (rootPhase 409) := by
  have hh := CBox.mul_contains_g mid409_contains root1_contains (c:=root409) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root410_contains : root410.Contains (rootPhase 410) := by
  have hh := CBox.mul_contains_g root205_contains root205_contains (c:=root410) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid411_contains : mid411.Contains (rootPhase 410) := root410_contains
lemma root411_contains : root411.Contains (rootPhase 411) := by
  have hh := CBox.mul_contains_g mid411_contains root1_contains (c:=root411) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root412_contains : root412.Contains (rootPhase 412) := by
  have hh := CBox.mul_contains_g root206_contains root206_contains (c:=root412) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid413_contains : mid413.Contains (rootPhase 412) := root412_contains
lemma root413_contains : root413.Contains (rootPhase 413) := by
  have hh := CBox.mul_contains_g mid413_contains root1_contains (c:=root413) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root414_contains : root414.Contains (rootPhase 414) := by
  have hh := CBox.mul_contains_g root207_contains root207_contains (c:=root414) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid415_contains : mid415.Contains (rootPhase 414) := root414_contains
lemma root415_contains : root415.Contains (rootPhase 415) := by
  have hh := CBox.mul_contains_g mid415_contains root1_contains (c:=root415) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root800_contains : root800.Contains (rootPhase 800) := by
  have hh := CBox.mul_contains_g root400_contains root400_contains (c:=root800) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid801_contains : mid801.Contains (rootPhase 800) := root800_contains
lemma root801_contains : root801.Contains (rootPhase 801) := by
  have hh := CBox.mul_contains_g mid801_contains root1_contains (c:=root801) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root802_contains : root802.Contains (rootPhase 802) := by
  have hh := CBox.mul_contains_g root401_contains root401_contains (c:=root802) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid803_contains : mid803.Contains (rootPhase 802) := root802_contains
lemma root803_contains : root803.Contains (rootPhase 803) := by
  have hh := CBox.mul_contains_g mid803_contains root1_contains (c:=root803) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root804_contains : root804.Contains (rootPhase 804) := by
  have hh := CBox.mul_contains_g root402_contains root402_contains (c:=root804) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid805_contains : mid805.Contains (rootPhase 804) := root804_contains
lemma root805_contains : root805.Contains (rootPhase 805) := by
  have hh := CBox.mul_contains_g mid805_contains root1_contains (c:=root805) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root806_contains : root806.Contains (rootPhase 806) := by
  have hh := CBox.mul_contains_g root403_contains root403_contains (c:=root806) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid807_contains : mid807.Contains (rootPhase 806) := root806_contains
lemma root807_contains : root807.Contains (rootPhase 807) := by
  have hh := CBox.mul_contains_g mid807_contains root1_contains (c:=root807) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root808_contains : root808.Contains (rootPhase 808) := by
  have hh := CBox.mul_contains_g root404_contains root404_contains (c:=root808) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid809_contains : mid809.Contains (rootPhase 808) := root808_contains
lemma root809_contains : root809.Contains (rootPhase 809) := by
  have hh := CBox.mul_contains_g mid809_contains root1_contains (c:=root809) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root810_contains : root810.Contains (rootPhase 810) := by
  have hh := CBox.mul_contains_g root405_contains root405_contains (c:=root810) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid811_contains : mid811.Contains (rootPhase 810) := root810_contains
lemma root811_contains : root811.Contains (rootPhase 811) := by
  have hh := CBox.mul_contains_g mid811_contains root1_contains (c:=root811) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root812_contains : root812.Contains (rootPhase 812) := by
  have hh := CBox.mul_contains_g root406_contains root406_contains (c:=root812) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid813_contains : mid813.Contains (rootPhase 812) := root812_contains
lemma root813_contains : root813.Contains (rootPhase 813) := by
  have hh := CBox.mul_contains_g mid813_contains root1_contains (c:=root813) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root814_contains : root814.Contains (rootPhase 814) := by
  have hh := CBox.mul_contains_g root407_contains root407_contains (c:=root814) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid815_contains : mid815.Contains (rootPhase 814) := root814_contains
lemma root815_contains : root815.Contains (rootPhase 815) := by
  have hh := CBox.mul_contains_g mid815_contains root1_contains (c:=root815) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root816_contains : root816.Contains (rootPhase 816) := by
  have hh := CBox.mul_contains_g root408_contains root408_contains (c:=root816) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid817_contains : mid817.Contains (rootPhase 816) := root816_contains
lemma root817_contains : root817.Contains (rootPhase 817) := by
  have hh := CBox.mul_contains_g mid817_contains root1_contains (c:=root817) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root818_contains : root818.Contains (rootPhase 818) := by
  have hh := CBox.mul_contains_g root409_contains root409_contains (c:=root818) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid819_contains : mid819.Contains (rootPhase 818) := root818_contains
lemma root819_contains : root819.Contains (rootPhase 819) := by
  have hh := CBox.mul_contains_g mid819_contains root1_contains (c:=root819) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root820_contains : root820.Contains (rootPhase 820) := by
  have hh := CBox.mul_contains_g root410_contains root410_contains (c:=root820) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid821_contains : mid821.Contains (rootPhase 820) := root820_contains
lemma root821_contains : root821.Contains (rootPhase 821) := by
  have hh := CBox.mul_contains_g mid821_contains root1_contains (c:=root821) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root822_contains : root822.Contains (rootPhase 822) := by
  have hh := CBox.mul_contains_g root411_contains root411_contains (c:=root822) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid823_contains : mid823.Contains (rootPhase 822) := root822_contains
lemma root823_contains : root823.Contains (rootPhase 823) := by
  have hh := CBox.mul_contains_g mid823_contains root1_contains (c:=root823) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root824_contains : root824.Contains (rootPhase 824) := by
  have hh := CBox.mul_contains_g root412_contains root412_contains (c:=root824) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid825_contains : mid825.Contains (rootPhase 824) := root824_contains
lemma root825_contains : root825.Contains (rootPhase 825) := by
  have hh := CBox.mul_contains_g mid825_contains root1_contains (c:=root825) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root826_contains : root826.Contains (rootPhase 826) := by
  have hh := CBox.mul_contains_g root413_contains root413_contains (c:=root826) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid827_contains : mid827.Contains (rootPhase 826) := root826_contains
lemma root827_contains : root827.Contains (rootPhase 827) := by
  have hh := CBox.mul_contains_g mid827_contains root1_contains (c:=root827) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root828_contains : root828.Contains (rootPhase 828) := by
  have hh := CBox.mul_contains_g root414_contains root414_contains (c:=root828) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid829_contains : mid829.Contains (rootPhase 828) := root828_contains
lemma root829_contains : root829.Contains (rootPhase 829) := by
  have hh := CBox.mul_contains_g mid829_contains root1_contains (c:=root829) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root830_contains : root830.Contains (rootPhase 830) := by
  have hh := CBox.mul_contains_g root415_contains root415_contains (c:=root830) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid831_contains : mid831.Contains (rootPhase 830) := root830_contains
lemma root831_contains : root831.Contains (rootPhase 831) := by
  have hh := CBox.mul_contains_g mid831_contains root1_contains (c:=root831) (by decide +kernel)
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
lemma roots25_contains_g_oai (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root800_contains
  · exact IntegerRoots.root801_contains
  · exact IntegerRoots.root802_contains
  · exact IntegerRoots.root803_contains
  · exact IntegerRoots.root804_contains
  · exact IntegerRoots.root805_contains
  · exact IntegerRoots.root806_contains
  · exact IntegerRoots.root807_contains
  · exact IntegerRoots.root808_contains
  · exact IntegerRoots.root809_contains
  · exact IntegerRoots.root810_contains
  · exact IntegerRoots.root811_contains
  · exact IntegerRoots.root812_contains
  · exact IntegerRoots.root813_contains
  · exact IntegerRoots.root814_contains
  · exact IntegerRoots.root815_contains
  · exact IntegerRoots.root816_contains
  · exact IntegerRoots.root817_contains
  · exact IntegerRoots.root818_contains
  · exact IntegerRoots.root819_contains
  · exact IntegerRoots.root820_contains
  · exact IntegerRoots.root821_contains
  · exact IntegerRoots.root822_contains
  · exact IntegerRoots.root823_contains
  · exact IntegerRoots.root824_contains
  · exact IntegerRoots.root825_contains
  · exact IntegerRoots.root826_contains
  · exact IntegerRoots.root827_contains
  · exact IntegerRoots.root828_contains
  · exact IntegerRoots.root829_contains
  · exact IntegerRoots.root830_contains
  · exact IntegerRoots.root831_contains
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.roots25_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.roots25_contains_g_oai
