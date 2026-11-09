-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row0_3_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:30.565174+00:00
-- url     : https://prove2.me/submissions/8ac48f51-8b60-46b3-9af6-0a09366a1819

import Mathlib
import Definitions.Def_OAIQ098G023
import Definitions.Def_OAIQ098G085
import Definitions.Def_OAIQ098G090
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G093
import Definitions.Def_OAIQ098G094
import Definitions.Def_OAIQ098G095
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots13_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerCompact_roots15_contains_g
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
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_scale_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
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

lemma rootPhase_periodic (n : ℕ) : rootPhase (n+1024) = rootPhase n := by
  unfold rootPhase
  have heq : Complex.I*Real.pi*(((n+1024:ℕ):ℂ)/512) =
    Complex.I*Real.pi*((n:ℂ)/512)+(2*Real.pi*Complex.I) := by push_cast <;> ring
  rw [heq,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma rootPhase_mod (n : ℕ) : rootPhase (n%1024) = rootPhase n := by
  have hp : Function.Periodic rootPhase 1024 := rootPhase_periodic
  exact hp.map_mod_nat n

lemma rootPhase_cos (n : ℕ) : (rootPhase n).re = Real.cos (Real.pi*((n:ℝ)/512)) := by
  unfold rootPhase
  rw [Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,
    Complex.natCast_im,zero_mul,mul_zero,sub_zero,zero_add,one_mul,
    zero_div,Real.exp_zero]


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
lemma root192_contains : root192.Contains (rootPhase 192) := by
  have hh := CBox.mul_contains_g root96_contains root96_contains (c:=root192) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid193_contains : mid193.Contains (rootPhase 192) := root192_contains
lemma root193_contains : root193.Contains (rootPhase 193) := by
  have hh := CBox.mul_contains_g mid193_contains root1_contains (c:=root193) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root194_contains : root194.Contains (rootPhase 194) := by
  have hh := CBox.mul_contains_g root97_contains root97_contains (c:=root194) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid195_contains : mid195.Contains (rootPhase 194) := root194_contains
lemma root195_contains : root195.Contains (rootPhase 195) := by
  have hh := CBox.mul_contains_g mid195_contains root1_contains (c:=root195) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root196_contains : root196.Contains (rootPhase 196) := by
  have hh := CBox.mul_contains_g root98_contains root98_contains (c:=root196) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid197_contains : mid197.Contains (rootPhase 196) := root196_contains
lemma root197_contains : root197.Contains (rootPhase 197) := by
  have hh := CBox.mul_contains_g mid197_contains root1_contains (c:=root197) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root198_contains : root198.Contains (rootPhase 198) := by
  have hh := CBox.mul_contains_g root99_contains root99_contains (c:=root198) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid199_contains : mid199.Contains (rootPhase 198) := root198_contains
lemma root199_contains : root199.Contains (rootPhase 199) := by
  have hh := CBox.mul_contains_g mid199_contains root1_contains (c:=root199) (by decide +kernel)
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
lemma root208_contains : root208.Contains (rootPhase 208) := by
  have hh := CBox.mul_contains_g root104_contains root104_contains (c:=root208) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid209_contains : mid209.Contains (rootPhase 208) := root208_contains
lemma root209_contains : root209.Contains (rootPhase 209) := by
  have hh := CBox.mul_contains_g mid209_contains root1_contains (c:=root209) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root210_contains : root210.Contains (rootPhase 210) := by
  have hh := CBox.mul_contains_g root105_contains root105_contains (c:=root210) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid211_contains : mid211.Contains (rootPhase 210) := root210_contains
lemma root211_contains : root211.Contains (rootPhase 211) := by
  have hh := CBox.mul_contains_g mid211_contains root1_contains (c:=root211) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root212_contains : root212.Contains (rootPhase 212) := by
  have hh := CBox.mul_contains_g root106_contains root106_contains (c:=root212) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid213_contains : mid213.Contains (rootPhase 212) := root212_contains
lemma root213_contains : root213.Contains (rootPhase 213) := by
  have hh := CBox.mul_contains_g mid213_contains root1_contains (c:=root213) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root214_contains : root214.Contains (rootPhase 214) := by
  have hh := CBox.mul_contains_g root107_contains root107_contains (c:=root214) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid215_contains : mid215.Contains (rootPhase 214) := root214_contains
lemma root215_contains : root215.Contains (rootPhase 215) := by
  have hh := CBox.mul_contains_g mid215_contains root1_contains (c:=root215) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root216_contains : root216.Contains (rootPhase 216) := by
  have hh := CBox.mul_contains_g root108_contains root108_contains (c:=root216) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid217_contains : mid217.Contains (rootPhase 216) := root216_contains
lemma root217_contains : root217.Contains (rootPhase 217) := by
  have hh := CBox.mul_contains_g mid217_contains root1_contains (c:=root217) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root218_contains : root218.Contains (rootPhase 218) := by
  have hh := CBox.mul_contains_g root109_contains root109_contains (c:=root218) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid219_contains : mid219.Contains (rootPhase 218) := root218_contains
lemma root219_contains : root219.Contains (rootPhase 219) := by
  have hh := CBox.mul_contains_g mid219_contains root1_contains (c:=root219) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root220_contains : root220.Contains (rootPhase 220) := by
  have hh := CBox.mul_contains_g root110_contains root110_contains (c:=root220) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid221_contains : mid221.Contains (rootPhase 220) := root220_contains
lemma root221_contains : root221.Contains (rootPhase 221) := by
  have hh := CBox.mul_contains_g mid221_contains root1_contains (c:=root221) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root222_contains : root222.Contains (rootPhase 222) := by
  have hh := CBox.mul_contains_g root111_contains root111_contains (c:=root222) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid223_contains : mid223.Contains (rootPhase 222) := root222_contains
lemma root223_contains : root223.Contains (rootPhase 223) := by
  have hh := CBox.mul_contains_g mid223_contains root1_contains (c:=root223) (by decide +kernel)
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
lemma root288_contains : root288.Contains (rootPhase 288) := by
  have hh := CBox.mul_contains_g root144_contains root144_contains (c:=root288) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid289_contains : mid289.Contains (rootPhase 288) := root288_contains
lemma root289_contains : root289.Contains (rootPhase 289) := by
  have hh := CBox.mul_contains_g mid289_contains root1_contains (c:=root289) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root290_contains : root290.Contains (rootPhase 290) := by
  have hh := CBox.mul_contains_g root145_contains root145_contains (c:=root290) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid291_contains : mid291.Contains (rootPhase 290) := root290_contains
lemma root291_contains : root291.Contains (rootPhase 291) := by
  have hh := CBox.mul_contains_g mid291_contains root1_contains (c:=root291) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root292_contains : root292.Contains (rootPhase 292) := by
  have hh := CBox.mul_contains_g root146_contains root146_contains (c:=root292) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid293_contains : mid293.Contains (rootPhase 292) := root292_contains
lemma root293_contains : root293.Contains (rootPhase 293) := by
  have hh := CBox.mul_contains_g mid293_contains root1_contains (c:=root293) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root294_contains : root294.Contains (rootPhase 294) := by
  have hh := CBox.mul_contains_g root147_contains root147_contains (c:=root294) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid295_contains : mid295.Contains (rootPhase 294) := root294_contains
lemma root295_contains : root295.Contains (rootPhase 295) := by
  have hh := CBox.mul_contains_g mid295_contains root1_contains (c:=root295) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root296_contains : root296.Contains (rootPhase 296) := by
  have hh := CBox.mul_contains_g root148_contains root148_contains (c:=root296) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid297_contains : mid297.Contains (rootPhase 296) := root296_contains
lemma root297_contains : root297.Contains (rootPhase 297) := by
  have hh := CBox.mul_contains_g mid297_contains root1_contains (c:=root297) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root298_contains : root298.Contains (rootPhase 298) := by
  have hh := CBox.mul_contains_g root149_contains root149_contains (c:=root298) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid299_contains : mid299.Contains (rootPhase 298) := root298_contains
lemma root299_contains : root299.Contains (rootPhase 299) := by
  have hh := CBox.mul_contains_g mid299_contains root1_contains (c:=root299) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root300_contains : root300.Contains (rootPhase 300) := by
  have hh := CBox.mul_contains_g root150_contains root150_contains (c:=root300) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid301_contains : mid301.Contains (rootPhase 300) := root300_contains
lemma root301_contains : root301.Contains (rootPhase 301) := by
  have hh := CBox.mul_contains_g mid301_contains root1_contains (c:=root301) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root302_contains : root302.Contains (rootPhase 302) := by
  have hh := CBox.mul_contains_g root151_contains root151_contains (c:=root302) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid303_contains : mid303.Contains (rootPhase 302) := root302_contains
lemma root303_contains : root303.Contains (rootPhase 303) := by
  have hh := CBox.mul_contains_g mid303_contains root1_contains (c:=root303) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root304_contains : root304.Contains (rootPhase 304) := by
  have hh := CBox.mul_contains_g root152_contains root152_contains (c:=root304) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid305_contains : mid305.Contains (rootPhase 304) := root304_contains
lemma root305_contains : root305.Contains (rootPhase 305) := by
  have hh := CBox.mul_contains_g mid305_contains root1_contains (c:=root305) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root306_contains : root306.Contains (rootPhase 306) := by
  have hh := CBox.mul_contains_g root153_contains root153_contains (c:=root306) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid307_contains : mid307.Contains (rootPhase 306) := root306_contains
lemma root307_contains : root307.Contains (rootPhase 307) := by
  have hh := CBox.mul_contains_g mid307_contains root1_contains (c:=root307) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root308_contains : root308.Contains (rootPhase 308) := by
  have hh := CBox.mul_contains_g root154_contains root154_contains (c:=root308) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid309_contains : mid309.Contains (rootPhase 308) := root308_contains
lemma root309_contains : root309.Contains (rootPhase 309) := by
  have hh := CBox.mul_contains_g mid309_contains root1_contains (c:=root309) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root310_contains : root310.Contains (rootPhase 310) := by
  have hh := CBox.mul_contains_g root155_contains root155_contains (c:=root310) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid311_contains : mid311.Contains (rootPhase 310) := root310_contains
lemma root311_contains : root311.Contains (rootPhase 311) := by
  have hh := CBox.mul_contains_g mid311_contains root1_contains (c:=root311) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root312_contains : root312.Contains (rootPhase 312) := by
  have hh := CBox.mul_contains_g root156_contains root156_contains (c:=root312) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid313_contains : mid313.Contains (rootPhase 312) := root312_contains
lemma root313_contains : root313.Contains (rootPhase 313) := by
  have hh := CBox.mul_contains_g mid313_contains root1_contains (c:=root313) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root314_contains : root314.Contains (rootPhase 314) := by
  have hh := CBox.mul_contains_g root157_contains root157_contains (c:=root314) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid315_contains : mid315.Contains (rootPhase 314) := root314_contains
lemma root315_contains : root315.Contains (rootPhase 315) := by
  have hh := CBox.mul_contains_g mid315_contains root1_contains (c:=root315) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root316_contains : root316.Contains (rootPhase 316) := by
  have hh := CBox.mul_contains_g root158_contains root158_contains (c:=root316) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid317_contains : mid317.Contains (rootPhase 316) := root316_contains
lemma root317_contains : root317.Contains (rootPhase 317) := by
  have hh := CBox.mul_contains_g mid317_contains root1_contains (c:=root317) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root318_contains : root318.Contains (rootPhase 318) := by
  have hh := CBox.mul_contains_g root159_contains root159_contains (c:=root318) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid319_contains : mid319.Contains (rootPhase 318) := root318_contains
lemma root319_contains : root319.Contains (rootPhase 319) := by
  have hh := CBox.mul_contains_g mid319_contains root1_contains (c:=root319) (by decide +kernel)
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
lemma root336_contains : root336.Contains (rootPhase 336) := by
  have hh := CBox.mul_contains_g root168_contains root168_contains (c:=root336) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid337_contains : mid337.Contains (rootPhase 336) := root336_contains
lemma root337_contains : root337.Contains (rootPhase 337) := by
  have hh := CBox.mul_contains_g mid337_contains root1_contains (c:=root337) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root338_contains : root338.Contains (rootPhase 338) := by
  have hh := CBox.mul_contains_g root169_contains root169_contains (c:=root338) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid339_contains : mid339.Contains (rootPhase 338) := root338_contains
lemma root339_contains : root339.Contains (rootPhase 339) := by
  have hh := CBox.mul_contains_g mid339_contains root1_contains (c:=root339) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root340_contains : root340.Contains (rootPhase 340) := by
  have hh := CBox.mul_contains_g root170_contains root170_contains (c:=root340) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid341_contains : mid341.Contains (rootPhase 340) := root340_contains
lemma root341_contains : root341.Contains (rootPhase 341) := by
  have hh := CBox.mul_contains_g mid341_contains root1_contains (c:=root341) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root342_contains : root342.Contains (rootPhase 342) := by
  have hh := CBox.mul_contains_g root171_contains root171_contains (c:=root342) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid343_contains : mid343.Contains (rootPhase 342) := root342_contains
lemma root343_contains : root343.Contains (rootPhase 343) := by
  have hh := CBox.mul_contains_g mid343_contains root1_contains (c:=root343) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root344_contains : root344.Contains (rootPhase 344) := by
  have hh := CBox.mul_contains_g root172_contains root172_contains (c:=root344) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid345_contains : mid345.Contains (rootPhase 344) := root344_contains
lemma root345_contains : root345.Contains (rootPhase 345) := by
  have hh := CBox.mul_contains_g mid345_contains root1_contains (c:=root345) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root346_contains : root346.Contains (rootPhase 346) := by
  have hh := CBox.mul_contains_g root173_contains root173_contains (c:=root346) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid347_contains : mid347.Contains (rootPhase 346) := root346_contains
lemma root347_contains : root347.Contains (rootPhase 347) := by
  have hh := CBox.mul_contains_g mid347_contains root1_contains (c:=root347) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root348_contains : root348.Contains (rootPhase 348) := by
  have hh := CBox.mul_contains_g root174_contains root174_contains (c:=root348) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid349_contains : mid349.Contains (rootPhase 348) := root348_contains
lemma root349_contains : root349.Contains (rootPhase 349) := by
  have hh := CBox.mul_contains_g mid349_contains root1_contains (c:=root349) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root350_contains : root350.Contains (rootPhase 350) := by
  have hh := CBox.mul_contains_g root175_contains root175_contains (c:=root350) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid351_contains : mid351.Contains (rootPhase 350) := root350_contains
lemma root351_contains : root351.Contains (rootPhase 351) := by
  have hh := CBox.mul_contains_g mid351_contains root1_contains (c:=root351) (by decide +kernel)
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
lemma root384_contains : root384.Contains (rootPhase 384) := by
  have hh := CBox.mul_contains_g root192_contains root192_contains (c:=root384) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid385_contains : mid385.Contains (rootPhase 384) := root384_contains
lemma root385_contains : root385.Contains (rootPhase 385) := by
  have hh := CBox.mul_contains_g mid385_contains root1_contains (c:=root385) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root386_contains : root386.Contains (rootPhase 386) := by
  have hh := CBox.mul_contains_g root193_contains root193_contains (c:=root386) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid387_contains : mid387.Contains (rootPhase 386) := root386_contains
lemma root387_contains : root387.Contains (rootPhase 387) := by
  have hh := CBox.mul_contains_g mid387_contains root1_contains (c:=root387) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root388_contains : root388.Contains (rootPhase 388) := by
  have hh := CBox.mul_contains_g root194_contains root194_contains (c:=root388) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid389_contains : mid389.Contains (rootPhase 388) := root388_contains
lemma root389_contains : root389.Contains (rootPhase 389) := by
  have hh := CBox.mul_contains_g mid389_contains root1_contains (c:=root389) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root390_contains : root390.Contains (rootPhase 390) := by
  have hh := CBox.mul_contains_g root195_contains root195_contains (c:=root390) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid391_contains : mid391.Contains (rootPhase 390) := root390_contains
lemma root391_contains : root391.Contains (rootPhase 391) := by
  have hh := CBox.mul_contains_g mid391_contains root1_contains (c:=root391) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root392_contains : root392.Contains (rootPhase 392) := by
  have hh := CBox.mul_contains_g root196_contains root196_contains (c:=root392) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid393_contains : mid393.Contains (rootPhase 392) := root392_contains
lemma root393_contains : root393.Contains (rootPhase 393) := by
  have hh := CBox.mul_contains_g mid393_contains root1_contains (c:=root393) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root394_contains : root394.Contains (rootPhase 394) := by
  have hh := CBox.mul_contains_g root197_contains root197_contains (c:=root394) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid395_contains : mid395.Contains (rootPhase 394) := root394_contains
lemma root395_contains : root395.Contains (rootPhase 395) := by
  have hh := CBox.mul_contains_g mid395_contains root1_contains (c:=root395) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root396_contains : root396.Contains (rootPhase 396) := by
  have hh := CBox.mul_contains_g root198_contains root198_contains (c:=root396) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid397_contains : mid397.Contains (rootPhase 396) := root396_contains
lemma root397_contains : root397.Contains (rootPhase 397) := by
  have hh := CBox.mul_contains_g mid397_contains root1_contains (c:=root397) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root398_contains : root398.Contains (rootPhase 398) := by
  have hh := CBox.mul_contains_g root199_contains root199_contains (c:=root398) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid399_contains : mid399.Contains (rootPhase 398) := root398_contains
lemma root399_contains : root399.Contains (rootPhase 399) := by
  have hh := CBox.mul_contains_g mid399_contains root1_contains (c:=root399) (by decide +kernel)
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

namespace SharpPlanar
open IntegerIntervals

lemma fejerNode_root (v : ℕ) : fejerNode v = (rootPhase (2*v+1)).re := by
  rw [rootPhase_cos]
  unfold fejerNode fejerAngle
  congr 1
  push_cast
  ring

end SharpPlanar

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
lemma roots6_contains (j : Fin 32) : (roots6 j).Contains (rootPhase (192+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root192_contains
  · exact IntegerRoots.root193_contains
  · exact IntegerRoots.root194_contains
  · exact IntegerRoots.root195_contains
  · exact IntegerRoots.root196_contains
  · exact IntegerRoots.root197_contains
  · exact IntegerRoots.root198_contains
  · exact IntegerRoots.root199_contains
  · exact IntegerRoots.root200_contains
  · exact IntegerRoots.root201_contains
  · exact IntegerRoots.root202_contains
  · exact IntegerRoots.root203_contains
  · exact IntegerRoots.root204_contains
  · exact IntegerRoots.root205_contains
  · exact IntegerRoots.root206_contains
  · exact IntegerRoots.root207_contains
  · exact IntegerRoots.root208_contains
  · exact IntegerRoots.root209_contains
  · exact IntegerRoots.root210_contains
  · exact IntegerRoots.root211_contains
  · exact IntegerRoots.root212_contains
  · exact IntegerRoots.root213_contains
  · exact IntegerRoots.root214_contains
  · exact IntegerRoots.root215_contains
  · exact IntegerRoots.root216_contains
  · exact IntegerRoots.root217_contains
  · exact IntegerRoots.root218_contains
  · exact IntegerRoots.root219_contains
  · exact IntegerRoots.root220_contains
  · exact IntegerRoots.root221_contains
  · exact IntegerRoots.root222_contains
  · exact IntegerRoots.root223_contains
lemma roots7_contains (j : Fin 32) : (roots7 j).Contains (rootPhase (224+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root224_contains
  · exact IntegerRoots.root225_contains
  · exact IntegerRoots.root226_contains
  · exact IntegerRoots.root227_contains
  · exact IntegerRoots.root228_contains
  · exact IntegerRoots.root229_contains
  · exact IntegerRoots.root230_contains
  · exact IntegerRoots.root231_contains
  · exact IntegerRoots.root232_contains
  · exact IntegerRoots.root233_contains
  · exact IntegerRoots.root234_contains
  · exact IntegerRoots.root235_contains
  · exact IntegerRoots.root236_contains
  · exact IntegerRoots.root237_contains
  · exact IntegerRoots.root238_contains
  · exact IntegerRoots.root239_contains
  · exact IntegerRoots.root240_contains
  · exact IntegerRoots.root241_contains
  · exact IntegerRoots.root242_contains
  · exact IntegerRoots.root243_contains
  · exact IntegerRoots.root244_contains
  · exact IntegerRoots.root245_contains
  · exact IntegerRoots.root246_contains
  · exact IntegerRoots.root247_contains
  · exact IntegerRoots.root248_contains
  · exact IntegerRoots.root249_contains
  · exact IntegerRoots.root250_contains
  · exact IntegerRoots.root251_contains
  · exact IntegerRoots.root252_contains
  · exact IntegerRoots.root253_contains
  · exact IntegerRoots.root254_contains
  · exact IntegerRoots.root255_contains
lemma roots8_contains (j : Fin 32) : (roots8 j).Contains (rootPhase (256+j.val)) := by
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
lemma roots9_contains (j : Fin 32) : (roots9 j).Contains (rootPhase (288+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root288_contains
  · exact IntegerRoots.root289_contains
  · exact IntegerRoots.root290_contains
  · exact IntegerRoots.root291_contains
  · exact IntegerRoots.root292_contains
  · exact IntegerRoots.root293_contains
  · exact IntegerRoots.root294_contains
  · exact IntegerRoots.root295_contains
  · exact IntegerRoots.root296_contains
  · exact IntegerRoots.root297_contains
  · exact IntegerRoots.root298_contains
  · exact IntegerRoots.root299_contains
  · exact IntegerRoots.root300_contains
  · exact IntegerRoots.root301_contains
  · exact IntegerRoots.root302_contains
  · exact IntegerRoots.root303_contains
  · exact IntegerRoots.root304_contains
  · exact IntegerRoots.root305_contains
  · exact IntegerRoots.root306_contains
  · exact IntegerRoots.root307_contains
  · exact IntegerRoots.root308_contains
  · exact IntegerRoots.root309_contains
  · exact IntegerRoots.root310_contains
  · exact IntegerRoots.root311_contains
  · exact IntegerRoots.root312_contains
  · exact IntegerRoots.root313_contains
  · exact IntegerRoots.root314_contains
  · exact IntegerRoots.root315_contains
  · exact IntegerRoots.root316_contains
  · exact IntegerRoots.root317_contains
  · exact IntegerRoots.root318_contains
  · exact IntegerRoots.root319_contains
lemma roots10_contains (j : Fin 32) : (roots10 j).Contains (rootPhase (320+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root320_contains
  · exact IntegerRoots.root321_contains
  · exact IntegerRoots.root322_contains
  · exact IntegerRoots.root323_contains
  · exact IntegerRoots.root324_contains
  · exact IntegerRoots.root325_contains
  · exact IntegerRoots.root326_contains
  · exact IntegerRoots.root327_contains
  · exact IntegerRoots.root328_contains
  · exact IntegerRoots.root329_contains
  · exact IntegerRoots.root330_contains
  · exact IntegerRoots.root331_contains
  · exact IntegerRoots.root332_contains
  · exact IntegerRoots.root333_contains
  · exact IntegerRoots.root334_contains
  · exact IntegerRoots.root335_contains
  · exact IntegerRoots.root336_contains
  · exact IntegerRoots.root337_contains
  · exact IntegerRoots.root338_contains
  · exact IntegerRoots.root339_contains
  · exact IntegerRoots.root340_contains
  · exact IntegerRoots.root341_contains
  · exact IntegerRoots.root342_contains
  · exact IntegerRoots.root343_contains
  · exact IntegerRoots.root344_contains
  · exact IntegerRoots.root345_contains
  · exact IntegerRoots.root346_contains
  · exact IntegerRoots.root347_contains
  · exact IntegerRoots.root348_contains
  · exact IntegerRoots.root349_contains
  · exact IntegerRoots.root350_contains
  · exact IntegerRoots.root351_contains
lemma roots11_contains (j : Fin 32) : (roots11 j).Contains (rootPhase (352+j.val)) := by
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
lemma roots12_contains (j : Fin 32) : (roots12 j).Contains (rootPhase (384+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root384_contains
  · exact IntegerRoots.root385_contains
  · exact IntegerRoots.root386_contains
  · exact IntegerRoots.root387_contains
  · exact IntegerRoots.root388_contains
  · exact IntegerRoots.root389_contains
  · exact IntegerRoots.root390_contains
  · exact IntegerRoots.root391_contains
  · exact IntegerRoots.root392_contains
  · exact IntegerRoots.root393_contains
  · exact IntegerRoots.root394_contains
  · exact IntegerRoots.root395_contains
  · exact IntegerRoots.root396_contains
  · exact IntegerRoots.root397_contains
  · exact IntegerRoots.root398_contains
  · exact IntegerRoots.root399_contains
  · exact IntegerRoots.root400_contains
  · exact IntegerRoots.root401_contains
  · exact IntegerRoots.root402_contains
  · exact IntegerRoots.root403_contains
  · exact IntegerRoots.root404_contains
  · exact IntegerRoots.root405_contains
  · exact IntegerRoots.root406_contains
  · exact IntegerRoots.root407_contains
  · exact IntegerRoots.root408_contains
  · exact IntegerRoots.root409_contains
  · exact IntegerRoots.root410_contains
  · exact IntegerRoots.root411_contains
  · exact IntegerRoots.root412_contains
  · exact IntegerRoots.root413_contains
  · exact IntegerRoots.root414_contains
  · exact IntegerRoots.root415_contains
lemma roots14_contains (j : Fin 32) : (roots14 j).Contains (rootPhase (448+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root448_contains
  · exact IntegerRoots.root449_contains
  · exact IntegerRoots.root450_contains
  · exact IntegerRoots.root451_contains
  · exact IntegerRoots.root452_contains
  · exact IntegerRoots.root453_contains
  · exact IntegerRoots.root454_contains
  · exact IntegerRoots.root455_contains
  · exact IntegerRoots.root456_contains
  · exact IntegerRoots.root457_contains
  · exact IntegerRoots.root458_contains
  · exact IntegerRoots.root459_contains
  · exact IntegerRoots.root460_contains
  · exact IntegerRoots.root461_contains
  · exact IntegerRoots.root462_contains
  · exact IntegerRoots.root463_contains
  · exact IntegerRoots.root464_contains
  · exact IntegerRoots.root465_contains
  · exact IntegerRoots.root466_contains
  · exact IntegerRoots.root467_contains
  · exact IntegerRoots.root468_contains
  · exact IntegerRoots.root469_contains
  · exact IntegerRoots.root470_contains
  · exact IntegerRoots.root471_contains
  · exact IntegerRoots.root472_contains
  · exact IntegerRoots.root473_contains
  · exact IntegerRoots.root474_contains
  · exact IntegerRoots.root475_contains
  · exact IntegerRoots.root476_contains
  · exact IntegerRoots.root477_contains
  · exact IntegerRoots.root478_contains
  · exact IntegerRoots.root479_contains
lemma roots16_contains (j : Fin 32) : (roots16 j).Contains (rootPhase (512+j.val)) := by
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
lemma rootRows_contains (i j : Fin 32) : (rootRows i j).Contains (rootPhase (32*i.val+j.val)) := by
  fin_cases i
  · exact roots0_contains j
  · exact roots1_contains j
  · exact roots2_contains j
  · exact roots3_contains j
  · exact roots4_contains j
  · exact roots5_contains j
  · exact roots6_contains j
  · exact roots7_contains j
  · exact roots8_contains j
  · exact roots9_contains j
  · exact roots10_contains j
  · exact roots11_contains j
  · exact roots12_contains j
  · exact roots13_contains_g j
  · exact roots14_contains j
  · exact roots15_contains_g j
  · exact roots16_contains j
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
lemma rootLookup_contains (n : ℕ) : (rootLookup n).Contains (rootPhase (n%1024)) := by
  have he : 32*((n%1024)/32)+n%32 = n%1024 := by omega
  simpa only [rootLookup,he] using rootRows_contains ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

lemma nodeLookup_contains (n : Fin 256) : (nodeLookup n).Contains (fejerNode n.val) := by
  have hh := (rootLookup_contains (2*n.val+1)).1
  rw [rootPhase_mod,← fejerNode_root] at hh
  exact hh
end SharpPlanar.IntegerCompact


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals IntegerCompact
lemma quadraturePoint_contains (j : ℕ) (v : Fin 256) :
    ((RBox.rat (2*(j:ℤ)+1) 12).add ((nodeLookup v).scale 1 12)).Contains
      (quadraturePoint j v.val) := by
  have hh := RBox.contains_add_g (RBox.contains_rat_g (2*(j:ℤ)+1) 12 (by norm_num))
    (RBox.contains_scale_g (nodeLookup_contains v) 1 12 (by norm_num))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold quadraturePoint
  push_cast
  ring

lemma p0_48_contains : p0_48.Contains (quadraturePoint 0 48) := by
  have ht : p0_48.t.Contains (quadraturePoint 0 48) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨48,by decide⟩).scale 1 12) = p0_48.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨48,by decide⟩
  have he : PointBox.calc p0_48.t = p0_48 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_49_contains : p0_49.Contains (quadraturePoint 0 49) := by
  have ht : p0_49.t.Contains (quadraturePoint 0 49) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨49,by decide⟩).scale 1 12) = p0_49.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨49,by decide⟩
  have he : PointBox.calc p0_49.t = p0_49 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_50_contains : p0_50.Contains (quadraturePoint 0 50) := by
  have ht : p0_50.t.Contains (quadraturePoint 0 50) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p0_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨50,by decide⟩
  have he : PointBox.calc p0_50.t = p0_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_51_contains : p0_51.Contains (quadraturePoint 0 51) := by
  have ht : p0_51.t.Contains (quadraturePoint 0 51) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨51,by decide⟩).scale 1 12) = p0_51.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨51,by decide⟩
  have he : PointBox.calc p0_51.t = p0_51 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_52_contains : p0_52.Contains (quadraturePoint 0 52) := by
  have ht : p0_52.t.Contains (quadraturePoint 0 52) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨52,by decide⟩).scale 1 12) = p0_52.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨52,by decide⟩
  have he : PointBox.calc p0_52.t = p0_52 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_53_contains : p0_53.Contains (quadraturePoint 0 53) := by
  have ht : p0_53.t.Contains (quadraturePoint 0 53) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨53,by decide⟩).scale 1 12) = p0_53.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨53,by decide⟩
  have he : PointBox.calc p0_53.t = p0_53 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_54_contains : p0_54.Contains (quadraturePoint 0 54) := by
  have ht : p0_54.t.Contains (quadraturePoint 0 54) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨54,by decide⟩).scale 1 12) = p0_54.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨54,by decide⟩
  have he : PointBox.calc p0_54.t = p0_54 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_55_contains : p0_55.Contains (quadraturePoint 0 55) := by
  have ht : p0_55.t.Contains (quadraturePoint 0 55) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨55,by decide⟩).scale 1 12) = p0_55.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨55,by decide⟩
  have he : PointBox.calc p0_55.t = p0_55 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_56_contains : p0_56.Contains (quadraturePoint 0 56) := by
  have ht : p0_56.t.Contains (quadraturePoint 0 56) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨56,by decide⟩).scale 1 12) = p0_56.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨56,by decide⟩
  have he : PointBox.calc p0_56.t = p0_56 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_57_contains : p0_57.Contains (quadraturePoint 0 57) := by
  have ht : p0_57.t.Contains (quadraturePoint 0 57) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨57,by decide⟩).scale 1 12) = p0_57.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨57,by decide⟩
  have he : PointBox.calc p0_57.t = p0_57 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_58_contains : p0_58.Contains (quadraturePoint 0 58) := by
  have ht : p0_58.t.Contains (quadraturePoint 0 58) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨58,by decide⟩).scale 1 12) = p0_58.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨58,by decide⟩
  have he : PointBox.calc p0_58.t = p0_58 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_59_contains : p0_59.Contains (quadraturePoint 0 59) := by
  have ht : p0_59.t.Contains (quadraturePoint 0 59) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨59,by decide⟩).scale 1 12) = p0_59.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨59,by decide⟩
  have he : PointBox.calc p0_59.t = p0_59 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_60_contains : p0_60.Contains (quadraturePoint 0 60) := by
  have ht : p0_60.t.Contains (quadraturePoint 0 60) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨60,by decide⟩).scale 1 12) = p0_60.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨60,by decide⟩
  have he : PointBox.calc p0_60.t = p0_60 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_61_contains : p0_61.Contains (quadraturePoint 0 61) := by
  have ht : p0_61.t.Contains (quadraturePoint 0 61) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨61,by decide⟩).scale 1 12) = p0_61.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨61,by decide⟩
  have he : PointBox.calc p0_61.t = p0_61 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_62_contains : p0_62.Contains (quadraturePoint 0 62) := by
  have ht : p0_62.t.Contains (quadraturePoint 0 62) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨62,by decide⟩).scale 1 12) = p0_62.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨62,by decide⟩
  have he : PointBox.calc p0_62.t = p0_62 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma p0_63_contains : p0_63.Contains (quadraturePoint 0 63) := by
  have ht : p0_63.t.Contains (quadraturePoint 0 63) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨63,by decide⟩).scale 1 12) = p0_63.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨63,by decide⟩
  have he : PointBox.calc p0_63.t = p0_63 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_g ht (by decide +kernel)

lemma row0_3_contains_g_oai (k : Fin 16) : (row0_3 k).Contains (quadraturePoint 0 (48+k.val)) := by
  fin_cases k
  · exact p0_48_contains
  · exact p0_49_contains
  · exact p0_50_contains
  · exact p0_51_contains
  · exact p0_52_contains
  · exact p0_53_contains
  · exact p0_54_contains
  · exact p0_55_contains
  · exact p0_56_contains
  · exact p0_57_contains
  · exact p0_58_contains
  · exact p0_59_contains
  · exact p0_60_contains
  · exact p0_61_contains
  · exact p0_62_contains
  · exact p0_63_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row0_3_contains_g_oai := @OAI.SharpPlanar.IntegerGrid.row0_3_contains_g_oai
