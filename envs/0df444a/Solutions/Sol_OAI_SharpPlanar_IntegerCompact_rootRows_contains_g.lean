-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerCompact.rootRows_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:07:00.763354+00:00
-- url     : https://prove2.me/submissions/3155c4e3-7deb-4810-b3ac-1d774283c25c

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G076
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G094
import Definitions.Def_OAIQ098G095
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots10_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots11_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots12_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots14_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots15_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots16_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots17_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots18_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots19_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots20_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots21_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots22_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots23_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots24_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots25_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots26_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots27_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots28_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots29_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots30_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots31_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots7_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots8_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots9_contains_g
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
lemma root0_contains : root0.Contains (rootPhase 0) := by
  simpa [rootPhase] using CBox.rat_contains_g (a:=root0) (mr:=1) (nr:=1) (mi:=0) (ni:=1) (by decide +kernel)
lemma root1_contains : root1.Contains (rootPhase 1) := phase_contains
lemma root2_contains : root2.Contains (rootPhase 2) := by
  have hh := CBox.mul_contains_g root1_contains root1_contains (c:=root2) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains_g mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains_g root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains_g mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains_g root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid7_contains : mid7.Contains (rootPhase 6) := root6_contains
lemma root7_contains : root7.Contains (rootPhase 7) := by
  have hh := CBox.mul_contains_g mid7_contains root1_contains (c:=root7) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains_g root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid9_contains : mid9.Contains (rootPhase 8) := root8_contains
lemma root9_contains : root9.Contains (rootPhase 9) := by
  have hh := CBox.mul_contains_g mid9_contains root1_contains (c:=root9) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains_g root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid11_contains : mid11.Contains (rootPhase 10) := root10_contains
lemma root11_contains : root11.Contains (rootPhase 11) := by
  have hh := CBox.mul_contains_g mid11_contains root1_contains (c:=root11) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains_g root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid13_contains : mid13.Contains (rootPhase 12) := root12_contains
lemma root13_contains : root13.Contains (rootPhase 13) := by
  have hh := CBox.mul_contains_g mid13_contains root1_contains (c:=root13) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root14_contains : root14.Contains (rootPhase 14) := by
  have hh := CBox.mul_contains_g root7_contains root7_contains (c:=root14) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid15_contains : mid15.Contains (rootPhase 14) := root14_contains
lemma root15_contains : root15.Contains (rootPhase 15) := by
  have hh := CBox.mul_contains_g mid15_contains root1_contains (c:=root15) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains_g root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid17_contains : mid17.Contains (rootPhase 16) := root16_contains
lemma root17_contains : root17.Contains (rootPhase 17) := by
  have hh := CBox.mul_contains_g mid17_contains root1_contains (c:=root17) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root18_contains : root18.Contains (rootPhase 18) := by
  have hh := CBox.mul_contains_g root9_contains root9_contains (c:=root18) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid19_contains : mid19.Contains (rootPhase 18) := root18_contains
lemma root19_contains : root19.Contains (rootPhase 19) := by
  have hh := CBox.mul_contains_g mid19_contains root1_contains (c:=root19) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root20_contains : root20.Contains (rootPhase 20) := by
  have hh := CBox.mul_contains_g root10_contains root10_contains (c:=root20) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid21_contains : mid21.Contains (rootPhase 20) := root20_contains
lemma root21_contains : root21.Contains (rootPhase 21) := by
  have hh := CBox.mul_contains_g mid21_contains root1_contains (c:=root21) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root22_contains : root22.Contains (rootPhase 22) := by
  have hh := CBox.mul_contains_g root11_contains root11_contains (c:=root22) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid23_contains : mid23.Contains (rootPhase 22) := root22_contains
lemma root23_contains : root23.Contains (rootPhase 23) := by
  have hh := CBox.mul_contains_g mid23_contains root1_contains (c:=root23) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains_g root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid25_contains : mid25.Contains (rootPhase 24) := root24_contains
lemma root25_contains : root25.Contains (rootPhase 25) := by
  have hh := CBox.mul_contains_g mid25_contains root1_contains (c:=root25) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root26_contains : root26.Contains (rootPhase 26) := by
  have hh := CBox.mul_contains_g root13_contains root13_contains (c:=root26) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid27_contains : mid27.Contains (rootPhase 26) := root26_contains
lemma root27_contains : root27.Contains (rootPhase 27) := by
  have hh := CBox.mul_contains_g mid27_contains root1_contains (c:=root27) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root28_contains : root28.Contains (rootPhase 28) := by
  have hh := CBox.mul_contains_g root14_contains root14_contains (c:=root28) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid29_contains : mid29.Contains (rootPhase 28) := root28_contains
lemma root29_contains : root29.Contains (rootPhase 29) := by
  have hh := CBox.mul_contains_g mid29_contains root1_contains (c:=root29) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root30_contains : root30.Contains (rootPhase 30) := by
  have hh := CBox.mul_contains_g root15_contains root15_contains (c:=root30) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid31_contains : mid31.Contains (rootPhase 30) := root30_contains
lemma root31_contains : root31.Contains (rootPhase 31) := by
  have hh := CBox.mul_contains_g mid31_contains root1_contains (c:=root31) (by decide +kernel)
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
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains_g root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains_g mid37_contains root1_contains (c:=root37) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root38_contains : root38.Contains (rootPhase 38) := by
  have hh := CBox.mul_contains_g root19_contains root19_contains (c:=root38) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid39_contains : mid39.Contains (rootPhase 38) := root38_contains
lemma root39_contains : root39.Contains (rootPhase 39) := by
  have hh := CBox.mul_contains_g mid39_contains root1_contains (c:=root39) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root40_contains : root40.Contains (rootPhase 40) := by
  have hh := CBox.mul_contains_g root20_contains root20_contains (c:=root40) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid41_contains : mid41.Contains (rootPhase 40) := root40_contains
lemma root41_contains : root41.Contains (rootPhase 41) := by
  have hh := CBox.mul_contains_g mid41_contains root1_contains (c:=root41) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root42_contains : root42.Contains (rootPhase 42) := by
  have hh := CBox.mul_contains_g root21_contains root21_contains (c:=root42) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid43_contains : mid43.Contains (rootPhase 42) := root42_contains
lemma root43_contains : root43.Contains (rootPhase 43) := by
  have hh := CBox.mul_contains_g mid43_contains root1_contains (c:=root43) (by decide +kernel)
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
lemma root48_contains : root48.Contains (rootPhase 48) := by
  have hh := CBox.mul_contains_g root24_contains root24_contains (c:=root48) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid49_contains : mid49.Contains (rootPhase 48) := root48_contains
lemma root49_contains : root49.Contains (rootPhase 49) := by
  have hh := CBox.mul_contains_g mid49_contains root1_contains (c:=root49) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root50_contains : root50.Contains (rootPhase 50) := by
  have hh := CBox.mul_contains_g root25_contains root25_contains (c:=root50) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid51_contains : mid51.Contains (rootPhase 50) := root50_contains
lemma root51_contains : root51.Contains (rootPhase 51) := by
  have hh := CBox.mul_contains_g mid51_contains root1_contains (c:=root51) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root52_contains : root52.Contains (rootPhase 52) := by
  have hh := CBox.mul_contains_g root26_contains root26_contains (c:=root52) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid53_contains : mid53.Contains (rootPhase 52) := root52_contains
lemma root53_contains : root53.Contains (rootPhase 53) := by
  have hh := CBox.mul_contains_g mid53_contains root1_contains (c:=root53) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root54_contains : root54.Contains (rootPhase 54) := by
  have hh := CBox.mul_contains_g root27_contains root27_contains (c:=root54) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid55_contains : mid55.Contains (rootPhase 54) := root54_contains
lemma root55_contains : root55.Contains (rootPhase 55) := by
  have hh := CBox.mul_contains_g mid55_contains root1_contains (c:=root55) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root56_contains : root56.Contains (rootPhase 56) := by
  have hh := CBox.mul_contains_g root28_contains root28_contains (c:=root56) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid57_contains : mid57.Contains (rootPhase 56) := root56_contains
lemma root57_contains : root57.Contains (rootPhase 57) := by
  have hh := CBox.mul_contains_g mid57_contains root1_contains (c:=root57) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root58_contains : root58.Contains (rootPhase 58) := by
  have hh := CBox.mul_contains_g root29_contains root29_contains (c:=root58) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid59_contains : mid59.Contains (rootPhase 58) := root58_contains
lemma root59_contains : root59.Contains (rootPhase 59) := by
  have hh := CBox.mul_contains_g mid59_contains root1_contains (c:=root59) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root60_contains : root60.Contains (rootPhase 60) := by
  have hh := CBox.mul_contains_g root30_contains root30_contains (c:=root60) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid61_contains : mid61.Contains (rootPhase 60) := root60_contains
lemma root61_contains : root61.Contains (rootPhase 61) := by
  have hh := CBox.mul_contains_g mid61_contains root1_contains (c:=root61) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root62_contains : root62.Contains (rootPhase 62) := by
  have hh := CBox.mul_contains_g root31_contains root31_contains (c:=root62) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid63_contains : mid63.Contains (rootPhase 62) := root62_contains
lemma root63_contains : root63.Contains (rootPhase 63) := by
  have hh := CBox.mul_contains_g mid63_contains root1_contains (c:=root63) (by decide +kernel)
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
lemma root72_contains : root72.Contains (rootPhase 72) := by
  have hh := CBox.mul_contains_g root36_contains root36_contains (c:=root72) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid73_contains : mid73.Contains (rootPhase 72) := root72_contains
lemma root73_contains : root73.Contains (rootPhase 73) := by
  have hh := CBox.mul_contains_g mid73_contains root1_contains (c:=root73) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root74_contains : root74.Contains (rootPhase 74) := by
  have hh := CBox.mul_contains_g root37_contains root37_contains (c:=root74) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid75_contains : mid75.Contains (rootPhase 74) := root74_contains
lemma root75_contains : root75.Contains (rootPhase 75) := by
  have hh := CBox.mul_contains_g mid75_contains root1_contains (c:=root75) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root76_contains : root76.Contains (rootPhase 76) := by
  have hh := CBox.mul_contains_g root38_contains root38_contains (c:=root76) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid77_contains : mid77.Contains (rootPhase 76) := root76_contains
lemma root77_contains : root77.Contains (rootPhase 77) := by
  have hh := CBox.mul_contains_g mid77_contains root1_contains (c:=root77) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root78_contains : root78.Contains (rootPhase 78) := by
  have hh := CBox.mul_contains_g root39_contains root39_contains (c:=root78) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid79_contains : mid79.Contains (rootPhase 78) := root78_contains
lemma root79_contains : root79.Contains (rootPhase 79) := by
  have hh := CBox.mul_contains_g mid79_contains root1_contains (c:=root79) (by decide +kernel)
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
lemma root84_contains : root84.Contains (rootPhase 84) := by
  have hh := CBox.mul_contains_g root42_contains root42_contains (c:=root84) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid85_contains : mid85.Contains (rootPhase 84) := root84_contains
lemma root85_contains : root85.Contains (rootPhase 85) := by
  have hh := CBox.mul_contains_g mid85_contains root1_contains (c:=root85) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root86_contains : root86.Contains (rootPhase 86) := by
  have hh := CBox.mul_contains_g root43_contains root43_contains (c:=root86) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid87_contains : mid87.Contains (rootPhase 86) := root86_contains
lemma root87_contains : root87.Contains (rootPhase 87) := by
  have hh := CBox.mul_contains_g mid87_contains root1_contains (c:=root87) (by decide +kernel)
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
lemma root104_contains : root104.Contains (rootPhase 104) := by
  have hh := CBox.mul_contains_g root52_contains root52_contains (c:=root104) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid105_contains : mid105.Contains (rootPhase 104) := root104_contains
lemma root105_contains : root105.Contains (rootPhase 105) := by
  have hh := CBox.mul_contains_g mid105_contains root1_contains (c:=root105) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root106_contains : root106.Contains (rootPhase 106) := by
  have hh := CBox.mul_contains_g root53_contains root53_contains (c:=root106) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid107_contains : mid107.Contains (rootPhase 106) := root106_contains
lemma root107_contains : root107.Contains (rootPhase 107) := by
  have hh := CBox.mul_contains_g mid107_contains root1_contains (c:=root107) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root108_contains : root108.Contains (rootPhase 108) := by
  have hh := CBox.mul_contains_g root54_contains root54_contains (c:=root108) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid109_contains : mid109.Contains (rootPhase 108) := root108_contains
lemma root109_contains : root109.Contains (rootPhase 109) := by
  have hh := CBox.mul_contains_g mid109_contains root1_contains (c:=root109) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root110_contains : root110.Contains (rootPhase 110) := by
  have hh := CBox.mul_contains_g root55_contains root55_contains (c:=root110) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid111_contains : mid111.Contains (rootPhase 110) := root110_contains
lemma root111_contains : root111.Contains (rootPhase 111) := by
  have hh := CBox.mul_contains_g mid111_contains root1_contains (c:=root111) (by decide +kernel)
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
lemma root144_contains : root144.Contains (rootPhase 144) := by
  have hh := CBox.mul_contains_g root72_contains root72_contains (c:=root144) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid145_contains : mid145.Contains (rootPhase 144) := root144_contains
lemma root145_contains : root145.Contains (rootPhase 145) := by
  have hh := CBox.mul_contains_g mid145_contains root1_contains (c:=root145) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root146_contains : root146.Contains (rootPhase 146) := by
  have hh := CBox.mul_contains_g root73_contains root73_contains (c:=root146) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid147_contains : mid147.Contains (rootPhase 146) := root146_contains
lemma root147_contains : root147.Contains (rootPhase 147) := by
  have hh := CBox.mul_contains_g mid147_contains root1_contains (c:=root147) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root148_contains : root148.Contains (rootPhase 148) := by
  have hh := CBox.mul_contains_g root74_contains root74_contains (c:=root148) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid149_contains : mid149.Contains (rootPhase 148) := root148_contains
lemma root149_contains : root149.Contains (rootPhase 149) := by
  have hh := CBox.mul_contains_g mid149_contains root1_contains (c:=root149) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root150_contains : root150.Contains (rootPhase 150) := by
  have hh := CBox.mul_contains_g root75_contains root75_contains (c:=root150) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid151_contains : mid151.Contains (rootPhase 150) := root150_contains
lemma root151_contains : root151.Contains (rootPhase 151) := by
  have hh := CBox.mul_contains_g mid151_contains root1_contains (c:=root151) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root152_contains : root152.Contains (rootPhase 152) := by
  have hh := CBox.mul_contains_g root76_contains root76_contains (c:=root152) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid153_contains : mid153.Contains (rootPhase 152) := root152_contains
lemma root153_contains : root153.Contains (rootPhase 153) := by
  have hh := CBox.mul_contains_g mid153_contains root1_contains (c:=root153) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root154_contains : root154.Contains (rootPhase 154) := by
  have hh := CBox.mul_contains_g root77_contains root77_contains (c:=root154) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid155_contains : mid155.Contains (rootPhase 154) := root154_contains
lemma root155_contains : root155.Contains (rootPhase 155) := by
  have hh := CBox.mul_contains_g mid155_contains root1_contains (c:=root155) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root156_contains : root156.Contains (rootPhase 156) := by
  have hh := CBox.mul_contains_g root78_contains root78_contains (c:=root156) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid157_contains : mid157.Contains (rootPhase 156) := root156_contains
lemma root157_contains : root157.Contains (rootPhase 157) := by
  have hh := CBox.mul_contains_g mid157_contains root1_contains (c:=root157) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root158_contains : root158.Contains (rootPhase 158) := by
  have hh := CBox.mul_contains_g root79_contains root79_contains (c:=root158) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid159_contains : mid159.Contains (rootPhase 158) := root158_contains
lemma root159_contains : root159.Contains (rootPhase 159) := by
  have hh := CBox.mul_contains_g mid159_contains root1_contains (c:=root159) (by decide +kernel)
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
lemma root168_contains : root168.Contains (rootPhase 168) := by
  have hh := CBox.mul_contains_g root84_contains root84_contains (c:=root168) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid169_contains : mid169.Contains (rootPhase 168) := root168_contains
lemma root169_contains : root169.Contains (rootPhase 169) := by
  have hh := CBox.mul_contains_g mid169_contains root1_contains (c:=root169) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root170_contains : root170.Contains (rootPhase 170) := by
  have hh := CBox.mul_contains_g root85_contains root85_contains (c:=root170) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid171_contains : mid171.Contains (rootPhase 170) := root170_contains
lemma root171_contains : root171.Contains (rootPhase 171) := by
  have hh := CBox.mul_contains_g mid171_contains root1_contains (c:=root171) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root172_contains : root172.Contains (rootPhase 172) := by
  have hh := CBox.mul_contains_g root86_contains root86_contains (c:=root172) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid173_contains : mid173.Contains (rootPhase 172) := root172_contains
lemma root173_contains : root173.Contains (rootPhase 173) := by
  have hh := CBox.mul_contains_g mid173_contains root1_contains (c:=root173) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root174_contains : root174.Contains (rootPhase 174) := by
  have hh := CBox.mul_contains_g root87_contains root87_contains (c:=root174) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid175_contains : mid175.Contains (rootPhase 174) := root174_contains
lemma root175_contains : root175.Contains (rootPhase 175) := by
  have hh := CBox.mul_contains_g mid175_contains root1_contains (c:=root175) (by decide +kernel)
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
lemma roots0_contains (j : Fin 32) : (roots0 j).Contains (rootPhase (0+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root0_contains
  · exact IntegerRoots.root1_contains
  · exact IntegerRoots.root2_contains
  · exact IntegerRoots.root3_contains
  · exact IntegerRoots.root4_contains
  · exact IntegerRoots.root5_contains
  · exact IntegerRoots.root6_contains
  · exact IntegerRoots.root7_contains
  · exact IntegerRoots.root8_contains
  · exact IntegerRoots.root9_contains
  · exact IntegerRoots.root10_contains
  · exact IntegerRoots.root11_contains
  · exact IntegerRoots.root12_contains
  · exact IntegerRoots.root13_contains
  · exact IntegerRoots.root14_contains
  · exact IntegerRoots.root15_contains
  · exact IntegerRoots.root16_contains
  · exact IntegerRoots.root17_contains
  · exact IntegerRoots.root18_contains
  · exact IntegerRoots.root19_contains
  · exact IntegerRoots.root20_contains
  · exact IntegerRoots.root21_contains
  · exact IntegerRoots.root22_contains
  · exact IntegerRoots.root23_contains
  · exact IntegerRoots.root24_contains
  · exact IntegerRoots.root25_contains
  · exact IntegerRoots.root26_contains
  · exact IntegerRoots.root27_contains
  · exact IntegerRoots.root28_contains
  · exact IntegerRoots.root29_contains
  · exact IntegerRoots.root30_contains
  · exact IntegerRoots.root31_contains
lemma roots1_contains (j : Fin 32) : (roots1 j).Contains (rootPhase (32+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root32_contains
  · exact IntegerRoots.root33_contains
  · exact IntegerRoots.root34_contains
  · exact IntegerRoots.root35_contains
  · exact IntegerRoots.root36_contains
  · exact IntegerRoots.root37_contains
  · exact IntegerRoots.root38_contains
  · exact IntegerRoots.root39_contains
  · exact IntegerRoots.root40_contains
  · exact IntegerRoots.root41_contains
  · exact IntegerRoots.root42_contains
  · exact IntegerRoots.root43_contains
  · exact IntegerRoots.root44_contains
  · exact IntegerRoots.root45_contains
  · exact IntegerRoots.root46_contains
  · exact IntegerRoots.root47_contains
  · exact IntegerRoots.root48_contains
  · exact IntegerRoots.root49_contains
  · exact IntegerRoots.root50_contains
  · exact IntegerRoots.root51_contains
  · exact IntegerRoots.root52_contains
  · exact IntegerRoots.root53_contains
  · exact IntegerRoots.root54_contains
  · exact IntegerRoots.root55_contains
  · exact IntegerRoots.root56_contains
  · exact IntegerRoots.root57_contains
  · exact IntegerRoots.root58_contains
  · exact IntegerRoots.root59_contains
  · exact IntegerRoots.root60_contains
  · exact IntegerRoots.root61_contains
  · exact IntegerRoots.root62_contains
  · exact IntegerRoots.root63_contains
lemma roots2_contains (j : Fin 32) : (roots2 j).Contains (rootPhase (64+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root64_contains
  · exact IntegerRoots.root65_contains
  · exact IntegerRoots.root66_contains
  · exact IntegerRoots.root67_contains
  · exact IntegerRoots.root68_contains
  · exact IntegerRoots.root69_contains
  · exact IntegerRoots.root70_contains
  · exact IntegerRoots.root71_contains
  · exact IntegerRoots.root72_contains
  · exact IntegerRoots.root73_contains
  · exact IntegerRoots.root74_contains
  · exact IntegerRoots.root75_contains
  · exact IntegerRoots.root76_contains
  · exact IntegerRoots.root77_contains
  · exact IntegerRoots.root78_contains
  · exact IntegerRoots.root79_contains
  · exact IntegerRoots.root80_contains
  · exact IntegerRoots.root81_contains
  · exact IntegerRoots.root82_contains
  · exact IntegerRoots.root83_contains
  · exact IntegerRoots.root84_contains
  · exact IntegerRoots.root85_contains
  · exact IntegerRoots.root86_contains
  · exact IntegerRoots.root87_contains
  · exact IntegerRoots.root88_contains
  · exact IntegerRoots.root89_contains
  · exact IntegerRoots.root90_contains
  · exact IntegerRoots.root91_contains
  · exact IntegerRoots.root92_contains
  · exact IntegerRoots.root93_contains
  · exact IntegerRoots.root94_contains
  · exact IntegerRoots.root95_contains
lemma roots3_contains (j : Fin 32) : (roots3 j).Contains (rootPhase (96+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root96_contains
  · exact IntegerRoots.root97_contains
  · exact IntegerRoots.root98_contains
  · exact IntegerRoots.root99_contains
  · exact IntegerRoots.root100_contains
  · exact IntegerRoots.root101_contains
  · exact IntegerRoots.root102_contains
  · exact IntegerRoots.root103_contains
  · exact IntegerRoots.root104_contains
  · exact IntegerRoots.root105_contains
  · exact IntegerRoots.root106_contains
  · exact IntegerRoots.root107_contains
  · exact IntegerRoots.root108_contains
  · exact IntegerRoots.root109_contains
  · exact IntegerRoots.root110_contains
  · exact IntegerRoots.root111_contains
  · exact IntegerRoots.root112_contains
  · exact IntegerRoots.root113_contains
  · exact IntegerRoots.root114_contains
  · exact IntegerRoots.root115_contains
  · exact IntegerRoots.root116_contains
  · exact IntegerRoots.root117_contains
  · exact IntegerRoots.root118_contains
  · exact IntegerRoots.root119_contains
  · exact IntegerRoots.root120_contains
  · exact IntegerRoots.root121_contains
  · exact IntegerRoots.root122_contains
  · exact IntegerRoots.root123_contains
  · exact IntegerRoots.root124_contains
  · exact IntegerRoots.root125_contains
  · exact IntegerRoots.root126_contains
  · exact IntegerRoots.root127_contains
lemma roots4_contains (j : Fin 32) : (roots4 j).Contains (rootPhase (128+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root128_contains
  · exact IntegerRoots.root129_contains
  · exact IntegerRoots.root130_contains
  · exact IntegerRoots.root131_contains
  · exact IntegerRoots.root132_contains
  · exact IntegerRoots.root133_contains
  · exact IntegerRoots.root134_contains
  · exact IntegerRoots.root135_contains
  · exact IntegerRoots.root136_contains
  · exact IntegerRoots.root137_contains
  · exact IntegerRoots.root138_contains
  · exact IntegerRoots.root139_contains
  · exact IntegerRoots.root140_contains
  · exact IntegerRoots.root141_contains
  · exact IntegerRoots.root142_contains
  · exact IntegerRoots.root143_contains
  · exact IntegerRoots.root144_contains
  · exact IntegerRoots.root145_contains
  · exact IntegerRoots.root146_contains
  · exact IntegerRoots.root147_contains
  · exact IntegerRoots.root148_contains
  · exact IntegerRoots.root149_contains
  · exact IntegerRoots.root150_contains
  · exact IntegerRoots.root151_contains
  · exact IntegerRoots.root152_contains
  · exact IntegerRoots.root153_contains
  · exact IntegerRoots.root154_contains
  · exact IntegerRoots.root155_contains
  · exact IntegerRoots.root156_contains
  · exact IntegerRoots.root157_contains
  · exact IntegerRoots.root158_contains
  · exact IntegerRoots.root159_contains
lemma roots5_contains (j : Fin 32) : (roots5 j).Contains (rootPhase (160+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root160_contains
  · exact IntegerRoots.root161_contains
  · exact IntegerRoots.root162_contains
  · exact IntegerRoots.root163_contains
  · exact IntegerRoots.root164_contains
  · exact IntegerRoots.root165_contains
  · exact IntegerRoots.root166_contains
  · exact IntegerRoots.root167_contains
  · exact IntegerRoots.root168_contains
  · exact IntegerRoots.root169_contains
  · exact IntegerRoots.root170_contains
  · exact IntegerRoots.root171_contains
  · exact IntegerRoots.root172_contains
  · exact IntegerRoots.root173_contains
  · exact IntegerRoots.root174_contains
  · exact IntegerRoots.root175_contains
  · exact IntegerRoots.root176_contains
  · exact IntegerRoots.root177_contains
  · exact IntegerRoots.root178_contains
  · exact IntegerRoots.root179_contains
  · exact IntegerRoots.root180_contains
  · exact IntegerRoots.root181_contains
  · exact IntegerRoots.root182_contains
  · exact IntegerRoots.root183_contains
  · exact IntegerRoots.root184_contains
  · exact IntegerRoots.root185_contains
  · exact IntegerRoots.root186_contains
  · exact IntegerRoots.root187_contains
  · exact IntegerRoots.root188_contains
  · exact IntegerRoots.root189_contains
  · exact IntegerRoots.root190_contains
  · exact IntegerRoots.root191_contains
lemma rootRows_contains_g_oai (i j : Fin 32) : (rootRows i j).Contains (rootPhase (32*i.val+j.val)) := by
  fin_cases i
  · exact roots0_contains j
  · exact roots1_contains j
  · exact roots2_contains j
  · exact roots3_contains j
  · exact roots4_contains j
  · exact roots5_contains j
  · exact roots6_contains_g j
  · exact roots7_contains_g j
  · exact roots8_contains_g j
  · exact roots9_contains_g j
  · exact roots10_contains_g j
  · exact roots11_contains_g j
  · exact roots12_contains_g j
  · exact roots13_contains_g j
  · exact roots14_contains_g j
  · exact roots15_contains_g j
  · exact roots16_contains_g j
  · exact roots17_contains_g j
  · exact roots18_contains_g j
  · exact roots19_contains_g j
  · exact roots20_contains_g j
  · exact roots21_contains_g j
  · exact roots22_contains_g j
  · exact roots23_contains_g j
  · exact roots24_contains_g j
  · exact roots25_contains_g j
  · exact roots26_contains_g j
  · exact roots27_contains_g j
  · exact roots28_contains_g j
  · exact roots29_contains_g j
  · exact roots30_contains_g j
  · exact roots31_contains_g j
end SharpPlanar.IntegerCompact


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerCompact.rootRows_contains_g_oai := @OAI.SharpPlanar.IntegerCompact.rootRows_contains_g_oai
