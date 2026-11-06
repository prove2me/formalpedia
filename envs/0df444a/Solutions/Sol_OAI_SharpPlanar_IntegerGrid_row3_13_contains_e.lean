-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerGrid.row3_13_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T03:05:01.11161+00:00
-- url     : https://prove2.me/submissions/5c4db727-cae2-4fe9-a972-dd19df3f6893

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_mul_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_rat_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_scale_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_PointBox_calc_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_add_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_scale_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_exp_from_horner_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_horner_step_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piBounds_contains_e

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
    c.Contains (z^(j+k)) := by rw [pow_add]; exact CBox.mul_contains_e ha hb hc


end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

lemma RBox.add_check (a b : RBox) : a.AddCheck b (a.add b) := ⟨le_rfl,le_rfl⟩
lemma RBox.contains_add {a b : RBox} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := RBox.add_contains_e hx hy (RBox.add_check _ _)

end SharpPlanar.IntegerIntervals

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
  · have hh := RBox.scale_contains_e piBounds_contains_e
      (c:=phaseInput.im) (m:=1) (n:=512) (by decide +kernel)
    simpa [div_eq_mul_inv,mul_comm] using hh
lemma small_contains : small.Contains ((1/2048:ℂ)*(Complex.I*Real.pi/512)) := by
  simpa using CBox.scale_contains_e phaseInput_contains (c:=small) (m:=1) (n:=2048) (by decide +kernel)
lemma h32 : poly32.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 32 0) := by
  simpa [expHorner,poly32,Nat.factorial] using CBox.rat_contains_e fact32_check
lemma h31 : poly31.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 31 1) := by
  exact horner_step_e small_contains h32 fact31_check (m:=mul31) (by decide +kernel) (by decide +kernel)
lemma h30 : poly30.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 30 2) := by
  exact horner_step_e small_contains h31 fact30_check (m:=mul30) (by decide +kernel) (by decide +kernel)
lemma h29 : poly29.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 29 3) := by
  exact horner_step_e small_contains h30 fact29_check (m:=mul29) (by decide +kernel) (by decide +kernel)
lemma h28 : poly28.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 28 4) := by
  exact horner_step_e small_contains h29 fact28_check (m:=mul28) (by decide +kernel) (by decide +kernel)
lemma h27 : poly27.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 27 5) := by
  exact horner_step_e small_contains h28 fact27_check (m:=mul27) (by decide +kernel) (by decide +kernel)
lemma h26 : poly26.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 26 6) := by
  exact horner_step_e small_contains h27 fact26_check (m:=mul26) (by decide +kernel) (by decide +kernel)
lemma h25 : poly25.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 25 7) := by
  exact horner_step_e small_contains h26 fact25_check (m:=mul25) (by decide +kernel) (by decide +kernel)
lemma h24 : poly24.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 24 8) := by
  exact horner_step_e small_contains h25 fact24_check (m:=mul24) (by decide +kernel) (by decide +kernel)
lemma h23 : poly23.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 23 9) := by
  exact horner_step_e small_contains h24 fact23_check (m:=mul23) (by decide +kernel) (by decide +kernel)
lemma h22 : poly22.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 22 10) := by
  exact horner_step_e small_contains h23 fact22_check (m:=mul22) (by decide +kernel) (by decide +kernel)
lemma h21 : poly21.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 21 11) := by
  exact horner_step_e small_contains h22 fact21_check (m:=mul21) (by decide +kernel) (by decide +kernel)
lemma h20 : poly20.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 20 12) := by
  exact horner_step_e small_contains h21 fact20_check (m:=mul20) (by decide +kernel) (by decide +kernel)
lemma h19 : poly19.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 19 13) := by
  exact horner_step_e small_contains h20 fact19_check (m:=mul19) (by decide +kernel) (by decide +kernel)
lemma h18 : poly18.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 18 14) := by
  exact horner_step_e small_contains h19 fact18_check (m:=mul18) (by decide +kernel) (by decide +kernel)
lemma h17 : poly17.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 17 15) := by
  exact horner_step_e small_contains h18 fact17_check (m:=mul17) (by decide +kernel) (by decide +kernel)
lemma h16 : poly16.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 16 16) := by
  exact horner_step_e small_contains h17 fact16_check (m:=mul16) (by decide +kernel) (by decide +kernel)
lemma h15 : poly15.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 15 17) := by
  exact horner_step_e small_contains h16 fact15_check (m:=mul15) (by decide +kernel) (by decide +kernel)
lemma h14 : poly14.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 14 18) := by
  exact horner_step_e small_contains h15 fact14_check (m:=mul14) (by decide +kernel) (by decide +kernel)
lemma h13 : poly13.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 13 19) := by
  exact horner_step_e small_contains h14 fact13_check (m:=mul13) (by decide +kernel) (by decide +kernel)
lemma h12 : poly12.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 12 20) := by
  exact horner_step_e small_contains h13 fact12_check (m:=mul12) (by decide +kernel) (by decide +kernel)
lemma h11 : poly11.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 11 21) := by
  exact horner_step_e small_contains h12 fact11_check (m:=mul11) (by decide +kernel) (by decide +kernel)
lemma h10 : poly10.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 10 22) := by
  exact horner_step_e small_contains h11 fact10_check (m:=mul10) (by decide +kernel) (by decide +kernel)
lemma h9 : poly9.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 9 23) := by
  exact horner_step_e small_contains h10 fact9_check (m:=mul9) (by decide +kernel) (by decide +kernel)
lemma h8 : poly8.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 8 24) := by
  exact horner_step_e small_contains h9 fact8_check (m:=mul8) (by decide +kernel) (by decide +kernel)
lemma h7 : poly7.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 7 25) := by
  exact horner_step_e small_contains h8 fact7_check (m:=mul7) (by decide +kernel) (by decide +kernel)
lemma h6 : poly6.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 6 26) := by
  exact horner_step_e small_contains h7 fact6_check (m:=mul6) (by decide +kernel) (by decide +kernel)
lemma h5 : poly5.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 5 27) := by
  exact horner_step_e small_contains h6 fact5_check (m:=mul5) (by decide +kernel) (by decide +kernel)
lemma h4 : poly4.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 4 28) := by
  exact horner_step_e small_contains h5 fact4_check (m:=mul4) (by decide +kernel) (by decide +kernel)
lemma h3 : poly3.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 3 29) := by
  exact horner_step_e small_contains h4 fact3_check (m:=mul3) (by decide +kernel) (by decide +kernel)
lemma h2 : poly2.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 2 30) := by
  exact horner_step_e small_contains h3 fact2_check (m:=mul2) (by decide +kernel) (by decide +kernel)
lemma h1 : poly1.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 1 31) := by
  exact horner_step_e small_contains h2 fact1_check (m:=mul1) (by decide +kernel) (by decide +kernel)
lemma h0 : poly0.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 0 32) := by
  exact horner_step_e small_contains h1 fact0_check (m:=mul0) (by decide +kernel) (by decide +kernel)
lemma sq0_contains : sq0.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^0)) := by
  simpa using exp_from_horner_e small_contains (b:=poly0) (c:=sq0) (by decide +kernel) h0 (by decide +kernel)
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
  simpa [rootPhase] using CBox.rat_contains_e (a:=root0) (mr:=1) (nr:=1) (mi:=0) (ni:=1) (by decide +kernel)
lemma root1_contains : root1.Contains (rootPhase 1) := phase_contains
lemma root2_contains : root2.Contains (rootPhase 2) := by
  have hh := CBox.mul_contains_e root1_contains root1_contains (c:=root2) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains_e mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains_e root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains_e mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains_e root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid7_contains : mid7.Contains (rootPhase 6) := root6_contains
lemma root7_contains : root7.Contains (rootPhase 7) := by
  have hh := CBox.mul_contains_e mid7_contains root1_contains (c:=root7) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains_e root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid9_contains : mid9.Contains (rootPhase 8) := root8_contains
lemma root9_contains : root9.Contains (rootPhase 9) := by
  have hh := CBox.mul_contains_e mid9_contains root1_contains (c:=root9) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains_e root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid11_contains : mid11.Contains (rootPhase 10) := root10_contains
lemma root11_contains : root11.Contains (rootPhase 11) := by
  have hh := CBox.mul_contains_e mid11_contains root1_contains (c:=root11) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains_e root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid13_contains : mid13.Contains (rootPhase 12) := root12_contains
lemma root13_contains : root13.Contains (rootPhase 13) := by
  have hh := CBox.mul_contains_e mid13_contains root1_contains (c:=root13) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root14_contains : root14.Contains (rootPhase 14) := by
  have hh := CBox.mul_contains_e root7_contains root7_contains (c:=root14) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid15_contains : mid15.Contains (rootPhase 14) := root14_contains
lemma root15_contains : root15.Contains (rootPhase 15) := by
  have hh := CBox.mul_contains_e mid15_contains root1_contains (c:=root15) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains_e root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid17_contains : mid17.Contains (rootPhase 16) := root16_contains
lemma root17_contains : root17.Contains (rootPhase 17) := by
  have hh := CBox.mul_contains_e mid17_contains root1_contains (c:=root17) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root18_contains : root18.Contains (rootPhase 18) := by
  have hh := CBox.mul_contains_e root9_contains root9_contains (c:=root18) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid19_contains : mid19.Contains (rootPhase 18) := root18_contains
lemma root19_contains : root19.Contains (rootPhase 19) := by
  have hh := CBox.mul_contains_e mid19_contains root1_contains (c:=root19) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root20_contains : root20.Contains (rootPhase 20) := by
  have hh := CBox.mul_contains_e root10_contains root10_contains (c:=root20) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid21_contains : mid21.Contains (rootPhase 20) := root20_contains
lemma root21_contains : root21.Contains (rootPhase 21) := by
  have hh := CBox.mul_contains_e mid21_contains root1_contains (c:=root21) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root22_contains : root22.Contains (rootPhase 22) := by
  have hh := CBox.mul_contains_e root11_contains root11_contains (c:=root22) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid23_contains : mid23.Contains (rootPhase 22) := root22_contains
lemma root23_contains : root23.Contains (rootPhase 23) := by
  have hh := CBox.mul_contains_e mid23_contains root1_contains (c:=root23) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains_e root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid25_contains : mid25.Contains (rootPhase 24) := root24_contains
lemma root25_contains : root25.Contains (rootPhase 25) := by
  have hh := CBox.mul_contains_e mid25_contains root1_contains (c:=root25) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root26_contains : root26.Contains (rootPhase 26) := by
  have hh := CBox.mul_contains_e root13_contains root13_contains (c:=root26) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid27_contains : mid27.Contains (rootPhase 26) := root26_contains
lemma root27_contains : root27.Contains (rootPhase 27) := by
  have hh := CBox.mul_contains_e mid27_contains root1_contains (c:=root27) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root28_contains : root28.Contains (rootPhase 28) := by
  have hh := CBox.mul_contains_e root14_contains root14_contains (c:=root28) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid29_contains : mid29.Contains (rootPhase 28) := root28_contains
lemma root29_contains : root29.Contains (rootPhase 29) := by
  have hh := CBox.mul_contains_e mid29_contains root1_contains (c:=root29) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root30_contains : root30.Contains (rootPhase 30) := by
  have hh := CBox.mul_contains_e root15_contains root15_contains (c:=root30) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid31_contains : mid31.Contains (rootPhase 30) := root30_contains
lemma root31_contains : root31.Contains (rootPhase 31) := by
  have hh := CBox.mul_contains_e mid31_contains root1_contains (c:=root31) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root32_contains : root32.Contains (rootPhase 32) := by
  have hh := CBox.mul_contains_e root16_contains root16_contains (c:=root32) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid33_contains : mid33.Contains (rootPhase 32) := root32_contains
lemma root33_contains : root33.Contains (rootPhase 33) := by
  have hh := CBox.mul_contains_e mid33_contains root1_contains (c:=root33) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root34_contains : root34.Contains (rootPhase 34) := by
  have hh := CBox.mul_contains_e root17_contains root17_contains (c:=root34) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid35_contains : mid35.Contains (rootPhase 34) := root34_contains
lemma root35_contains : root35.Contains (rootPhase 35) := by
  have hh := CBox.mul_contains_e mid35_contains root1_contains (c:=root35) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains_e root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains_e mid37_contains root1_contains (c:=root37) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root38_contains : root38.Contains (rootPhase 38) := by
  have hh := CBox.mul_contains_e root19_contains root19_contains (c:=root38) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid39_contains : mid39.Contains (rootPhase 38) := root38_contains
lemma root39_contains : root39.Contains (rootPhase 39) := by
  have hh := CBox.mul_contains_e mid39_contains root1_contains (c:=root39) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root40_contains : root40.Contains (rootPhase 40) := by
  have hh := CBox.mul_contains_e root20_contains root20_contains (c:=root40) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid41_contains : mid41.Contains (rootPhase 40) := root40_contains
lemma root41_contains : root41.Contains (rootPhase 41) := by
  have hh := CBox.mul_contains_e mid41_contains root1_contains (c:=root41) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root42_contains : root42.Contains (rootPhase 42) := by
  have hh := CBox.mul_contains_e root21_contains root21_contains (c:=root42) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid43_contains : mid43.Contains (rootPhase 42) := root42_contains
lemma root43_contains : root43.Contains (rootPhase 43) := by
  have hh := CBox.mul_contains_e mid43_contains root1_contains (c:=root43) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root44_contains : root44.Contains (rootPhase 44) := by
  have hh := CBox.mul_contains_e root22_contains root22_contains (c:=root44) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid45_contains : mid45.Contains (rootPhase 44) := root44_contains
lemma root45_contains : root45.Contains (rootPhase 45) := by
  have hh := CBox.mul_contains_e mid45_contains root1_contains (c:=root45) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root46_contains : root46.Contains (rootPhase 46) := by
  have hh := CBox.mul_contains_e root23_contains root23_contains (c:=root46) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid47_contains : mid47.Contains (rootPhase 46) := root46_contains
lemma root47_contains : root47.Contains (rootPhase 47) := by
  have hh := CBox.mul_contains_e mid47_contains root1_contains (c:=root47) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root48_contains : root48.Contains (rootPhase 48) := by
  have hh := CBox.mul_contains_e root24_contains root24_contains (c:=root48) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid49_contains : mid49.Contains (rootPhase 48) := root48_contains
lemma root49_contains : root49.Contains (rootPhase 49) := by
  have hh := CBox.mul_contains_e mid49_contains root1_contains (c:=root49) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root50_contains : root50.Contains (rootPhase 50) := by
  have hh := CBox.mul_contains_e root25_contains root25_contains (c:=root50) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid51_contains : mid51.Contains (rootPhase 50) := root50_contains
lemma root51_contains : root51.Contains (rootPhase 51) := by
  have hh := CBox.mul_contains_e mid51_contains root1_contains (c:=root51) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root52_contains : root52.Contains (rootPhase 52) := by
  have hh := CBox.mul_contains_e root26_contains root26_contains (c:=root52) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid53_contains : mid53.Contains (rootPhase 52) := root52_contains
lemma root53_contains : root53.Contains (rootPhase 53) := by
  have hh := CBox.mul_contains_e mid53_contains root1_contains (c:=root53) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root54_contains : root54.Contains (rootPhase 54) := by
  have hh := CBox.mul_contains_e root27_contains root27_contains (c:=root54) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid55_contains : mid55.Contains (rootPhase 54) := root54_contains
lemma root55_contains : root55.Contains (rootPhase 55) := by
  have hh := CBox.mul_contains_e mid55_contains root1_contains (c:=root55) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root56_contains : root56.Contains (rootPhase 56) := by
  have hh := CBox.mul_contains_e root28_contains root28_contains (c:=root56) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid57_contains : mid57.Contains (rootPhase 56) := root56_contains
lemma root57_contains : root57.Contains (rootPhase 57) := by
  have hh := CBox.mul_contains_e mid57_contains root1_contains (c:=root57) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root58_contains : root58.Contains (rootPhase 58) := by
  have hh := CBox.mul_contains_e root29_contains root29_contains (c:=root58) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid59_contains : mid59.Contains (rootPhase 58) := root58_contains
lemma root59_contains : root59.Contains (rootPhase 59) := by
  have hh := CBox.mul_contains_e mid59_contains root1_contains (c:=root59) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root60_contains : root60.Contains (rootPhase 60) := by
  have hh := CBox.mul_contains_e root30_contains root30_contains (c:=root60) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid61_contains : mid61.Contains (rootPhase 60) := root60_contains
lemma root61_contains : root61.Contains (rootPhase 61) := by
  have hh := CBox.mul_contains_e mid61_contains root1_contains (c:=root61) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root62_contains : root62.Contains (rootPhase 62) := by
  have hh := CBox.mul_contains_e root31_contains root31_contains (c:=root62) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid63_contains : mid63.Contains (rootPhase 62) := root62_contains
lemma root63_contains : root63.Contains (rootPhase 63) := by
  have hh := CBox.mul_contains_e mid63_contains root1_contains (c:=root63) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root64_contains : root64.Contains (rootPhase 64) := by
  have hh := CBox.mul_contains_e root32_contains root32_contains (c:=root64) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid65_contains : mid65.Contains (rootPhase 64) := root64_contains
lemma root65_contains : root65.Contains (rootPhase 65) := by
  have hh := CBox.mul_contains_e mid65_contains root1_contains (c:=root65) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root66_contains : root66.Contains (rootPhase 66) := by
  have hh := CBox.mul_contains_e root33_contains root33_contains (c:=root66) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid67_contains : mid67.Contains (rootPhase 66) := root66_contains
lemma root67_contains : root67.Contains (rootPhase 67) := by
  have hh := CBox.mul_contains_e mid67_contains root1_contains (c:=root67) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root68_contains : root68.Contains (rootPhase 68) := by
  have hh := CBox.mul_contains_e root34_contains root34_contains (c:=root68) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid69_contains : mid69.Contains (rootPhase 68) := root68_contains
lemma root69_contains : root69.Contains (rootPhase 69) := by
  have hh := CBox.mul_contains_e mid69_contains root1_contains (c:=root69) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root70_contains : root70.Contains (rootPhase 70) := by
  have hh := CBox.mul_contains_e root35_contains root35_contains (c:=root70) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid71_contains : mid71.Contains (rootPhase 70) := root70_contains
lemma root71_contains : root71.Contains (rootPhase 71) := by
  have hh := CBox.mul_contains_e mid71_contains root1_contains (c:=root71) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root72_contains : root72.Contains (rootPhase 72) := by
  have hh := CBox.mul_contains_e root36_contains root36_contains (c:=root72) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid73_contains : mid73.Contains (rootPhase 72) := root72_contains
lemma root73_contains : root73.Contains (rootPhase 73) := by
  have hh := CBox.mul_contains_e mid73_contains root1_contains (c:=root73) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root74_contains : root74.Contains (rootPhase 74) := by
  have hh := CBox.mul_contains_e root37_contains root37_contains (c:=root74) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid75_contains : mid75.Contains (rootPhase 74) := root74_contains
lemma root75_contains : root75.Contains (rootPhase 75) := by
  have hh := CBox.mul_contains_e mid75_contains root1_contains (c:=root75) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root76_contains : root76.Contains (rootPhase 76) := by
  have hh := CBox.mul_contains_e root38_contains root38_contains (c:=root76) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid77_contains : mid77.Contains (rootPhase 76) := root76_contains
lemma root77_contains : root77.Contains (rootPhase 77) := by
  have hh := CBox.mul_contains_e mid77_contains root1_contains (c:=root77) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root78_contains : root78.Contains (rootPhase 78) := by
  have hh := CBox.mul_contains_e root39_contains root39_contains (c:=root78) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid79_contains : mid79.Contains (rootPhase 78) := root78_contains
lemma root79_contains : root79.Contains (rootPhase 79) := by
  have hh := CBox.mul_contains_e mid79_contains root1_contains (c:=root79) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root80_contains : root80.Contains (rootPhase 80) := by
  have hh := CBox.mul_contains_e root40_contains root40_contains (c:=root80) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid81_contains : mid81.Contains (rootPhase 80) := root80_contains
lemma root81_contains : root81.Contains (rootPhase 81) := by
  have hh := CBox.mul_contains_e mid81_contains root1_contains (c:=root81) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root82_contains : root82.Contains (rootPhase 82) := by
  have hh := CBox.mul_contains_e root41_contains root41_contains (c:=root82) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid83_contains : mid83.Contains (rootPhase 82) := root82_contains
lemma root83_contains : root83.Contains (rootPhase 83) := by
  have hh := CBox.mul_contains_e mid83_contains root1_contains (c:=root83) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root84_contains : root84.Contains (rootPhase 84) := by
  have hh := CBox.mul_contains_e root42_contains root42_contains (c:=root84) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid85_contains : mid85.Contains (rootPhase 84) := root84_contains
lemma root85_contains : root85.Contains (rootPhase 85) := by
  have hh := CBox.mul_contains_e mid85_contains root1_contains (c:=root85) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root86_contains : root86.Contains (rootPhase 86) := by
  have hh := CBox.mul_contains_e root43_contains root43_contains (c:=root86) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid87_contains : mid87.Contains (rootPhase 86) := root86_contains
lemma root87_contains : root87.Contains (rootPhase 87) := by
  have hh := CBox.mul_contains_e mid87_contains root1_contains (c:=root87) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root88_contains : root88.Contains (rootPhase 88) := by
  have hh := CBox.mul_contains_e root44_contains root44_contains (c:=root88) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid89_contains : mid89.Contains (rootPhase 88) := root88_contains
lemma root89_contains : root89.Contains (rootPhase 89) := by
  have hh := CBox.mul_contains_e mid89_contains root1_contains (c:=root89) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root90_contains : root90.Contains (rootPhase 90) := by
  have hh := CBox.mul_contains_e root45_contains root45_contains (c:=root90) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid91_contains : mid91.Contains (rootPhase 90) := root90_contains
lemma root91_contains : root91.Contains (rootPhase 91) := by
  have hh := CBox.mul_contains_e mid91_contains root1_contains (c:=root91) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root92_contains : root92.Contains (rootPhase 92) := by
  have hh := CBox.mul_contains_e root46_contains root46_contains (c:=root92) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid93_contains : mid93.Contains (rootPhase 92) := root92_contains
lemma root93_contains : root93.Contains (rootPhase 93) := by
  have hh := CBox.mul_contains_e mid93_contains root1_contains (c:=root93) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root94_contains : root94.Contains (rootPhase 94) := by
  have hh := CBox.mul_contains_e root47_contains root47_contains (c:=root94) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid95_contains : mid95.Contains (rootPhase 94) := root94_contains
lemma root95_contains : root95.Contains (rootPhase 95) := by
  have hh := CBox.mul_contains_e mid95_contains root1_contains (c:=root95) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root96_contains : root96.Contains (rootPhase 96) := by
  have hh := CBox.mul_contains_e root48_contains root48_contains (c:=root96) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid97_contains : mid97.Contains (rootPhase 96) := root96_contains
lemma root97_contains : root97.Contains (rootPhase 97) := by
  have hh := CBox.mul_contains_e mid97_contains root1_contains (c:=root97) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root98_contains : root98.Contains (rootPhase 98) := by
  have hh := CBox.mul_contains_e root49_contains root49_contains (c:=root98) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid99_contains : mid99.Contains (rootPhase 98) := root98_contains
lemma root99_contains : root99.Contains (rootPhase 99) := by
  have hh := CBox.mul_contains_e mid99_contains root1_contains (c:=root99) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root100_contains : root100.Contains (rootPhase 100) := by
  have hh := CBox.mul_contains_e root50_contains root50_contains (c:=root100) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid101_contains : mid101.Contains (rootPhase 100) := root100_contains
lemma root101_contains : root101.Contains (rootPhase 101) := by
  have hh := CBox.mul_contains_e mid101_contains root1_contains (c:=root101) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root102_contains : root102.Contains (rootPhase 102) := by
  have hh := CBox.mul_contains_e root51_contains root51_contains (c:=root102) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid103_contains : mid103.Contains (rootPhase 102) := root102_contains
lemma root103_contains : root103.Contains (rootPhase 103) := by
  have hh := CBox.mul_contains_e mid103_contains root1_contains (c:=root103) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root104_contains : root104.Contains (rootPhase 104) := by
  have hh := CBox.mul_contains_e root52_contains root52_contains (c:=root104) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid105_contains : mid105.Contains (rootPhase 104) := root104_contains
lemma root105_contains : root105.Contains (rootPhase 105) := by
  have hh := CBox.mul_contains_e mid105_contains root1_contains (c:=root105) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root106_contains : root106.Contains (rootPhase 106) := by
  have hh := CBox.mul_contains_e root53_contains root53_contains (c:=root106) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid107_contains : mid107.Contains (rootPhase 106) := root106_contains
lemma root107_contains : root107.Contains (rootPhase 107) := by
  have hh := CBox.mul_contains_e mid107_contains root1_contains (c:=root107) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root108_contains : root108.Contains (rootPhase 108) := by
  have hh := CBox.mul_contains_e root54_contains root54_contains (c:=root108) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid109_contains : mid109.Contains (rootPhase 108) := root108_contains
lemma root109_contains : root109.Contains (rootPhase 109) := by
  have hh := CBox.mul_contains_e mid109_contains root1_contains (c:=root109) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root110_contains : root110.Contains (rootPhase 110) := by
  have hh := CBox.mul_contains_e root55_contains root55_contains (c:=root110) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid111_contains : mid111.Contains (rootPhase 110) := root110_contains
lemma root111_contains : root111.Contains (rootPhase 111) := by
  have hh := CBox.mul_contains_e mid111_contains root1_contains (c:=root111) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root112_contains : root112.Contains (rootPhase 112) := by
  have hh := CBox.mul_contains_e root56_contains root56_contains (c:=root112) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid113_contains : mid113.Contains (rootPhase 112) := root112_contains
lemma root113_contains : root113.Contains (rootPhase 113) := by
  have hh := CBox.mul_contains_e mid113_contains root1_contains (c:=root113) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root114_contains : root114.Contains (rootPhase 114) := by
  have hh := CBox.mul_contains_e root57_contains root57_contains (c:=root114) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid115_contains : mid115.Contains (rootPhase 114) := root114_contains
lemma root115_contains : root115.Contains (rootPhase 115) := by
  have hh := CBox.mul_contains_e mid115_contains root1_contains (c:=root115) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root116_contains : root116.Contains (rootPhase 116) := by
  have hh := CBox.mul_contains_e root58_contains root58_contains (c:=root116) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid117_contains : mid117.Contains (rootPhase 116) := root116_contains
lemma root117_contains : root117.Contains (rootPhase 117) := by
  have hh := CBox.mul_contains_e mid117_contains root1_contains (c:=root117) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root118_contains : root118.Contains (rootPhase 118) := by
  have hh := CBox.mul_contains_e root59_contains root59_contains (c:=root118) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid119_contains : mid119.Contains (rootPhase 118) := root118_contains
lemma root119_contains : root119.Contains (rootPhase 119) := by
  have hh := CBox.mul_contains_e mid119_contains root1_contains (c:=root119) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root120_contains : root120.Contains (rootPhase 120) := by
  have hh := CBox.mul_contains_e root60_contains root60_contains (c:=root120) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid121_contains : mid121.Contains (rootPhase 120) := root120_contains
lemma root121_contains : root121.Contains (rootPhase 121) := by
  have hh := CBox.mul_contains_e mid121_contains root1_contains (c:=root121) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root122_contains : root122.Contains (rootPhase 122) := by
  have hh := CBox.mul_contains_e root61_contains root61_contains (c:=root122) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid123_contains : mid123.Contains (rootPhase 122) := root122_contains
lemma root123_contains : root123.Contains (rootPhase 123) := by
  have hh := CBox.mul_contains_e mid123_contains root1_contains (c:=root123) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root124_contains : root124.Contains (rootPhase 124) := by
  have hh := CBox.mul_contains_e root62_contains root62_contains (c:=root124) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid125_contains : mid125.Contains (rootPhase 124) := root124_contains
lemma root125_contains : root125.Contains (rootPhase 125) := by
  have hh := CBox.mul_contains_e mid125_contains root1_contains (c:=root125) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root126_contains : root126.Contains (rootPhase 126) := by
  have hh := CBox.mul_contains_e root63_contains root63_contains (c:=root126) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid127_contains : mid127.Contains (rootPhase 126) := root126_contains
lemma root127_contains : root127.Contains (rootPhase 127) := by
  have hh := CBox.mul_contains_e mid127_contains root1_contains (c:=root127) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root128_contains : root128.Contains (rootPhase 128) := by
  have hh := CBox.mul_contains_e root64_contains root64_contains (c:=root128) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid129_contains : mid129.Contains (rootPhase 128) := root128_contains
lemma root129_contains : root129.Contains (rootPhase 129) := by
  have hh := CBox.mul_contains_e mid129_contains root1_contains (c:=root129) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root130_contains : root130.Contains (rootPhase 130) := by
  have hh := CBox.mul_contains_e root65_contains root65_contains (c:=root130) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid131_contains : mid131.Contains (rootPhase 130) := root130_contains
lemma root131_contains : root131.Contains (rootPhase 131) := by
  have hh := CBox.mul_contains_e mid131_contains root1_contains (c:=root131) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root132_contains : root132.Contains (rootPhase 132) := by
  have hh := CBox.mul_contains_e root66_contains root66_contains (c:=root132) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid133_contains : mid133.Contains (rootPhase 132) := root132_contains
lemma root133_contains : root133.Contains (rootPhase 133) := by
  have hh := CBox.mul_contains_e mid133_contains root1_contains (c:=root133) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root134_contains : root134.Contains (rootPhase 134) := by
  have hh := CBox.mul_contains_e root67_contains root67_contains (c:=root134) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid135_contains : mid135.Contains (rootPhase 134) := root134_contains
lemma root135_contains : root135.Contains (rootPhase 135) := by
  have hh := CBox.mul_contains_e mid135_contains root1_contains (c:=root135) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root136_contains : root136.Contains (rootPhase 136) := by
  have hh := CBox.mul_contains_e root68_contains root68_contains (c:=root136) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid137_contains : mid137.Contains (rootPhase 136) := root136_contains
lemma root137_contains : root137.Contains (rootPhase 137) := by
  have hh := CBox.mul_contains_e mid137_contains root1_contains (c:=root137) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root138_contains : root138.Contains (rootPhase 138) := by
  have hh := CBox.mul_contains_e root69_contains root69_contains (c:=root138) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid139_contains : mid139.Contains (rootPhase 138) := root138_contains
lemma root139_contains : root139.Contains (rootPhase 139) := by
  have hh := CBox.mul_contains_e mid139_contains root1_contains (c:=root139) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root140_contains : root140.Contains (rootPhase 140) := by
  have hh := CBox.mul_contains_e root70_contains root70_contains (c:=root140) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid141_contains : mid141.Contains (rootPhase 140) := root140_contains
lemma root141_contains : root141.Contains (rootPhase 141) := by
  have hh := CBox.mul_contains_e mid141_contains root1_contains (c:=root141) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root142_contains : root142.Contains (rootPhase 142) := by
  have hh := CBox.mul_contains_e root71_contains root71_contains (c:=root142) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid143_contains : mid143.Contains (rootPhase 142) := root142_contains
lemma root143_contains : root143.Contains (rootPhase 143) := by
  have hh := CBox.mul_contains_e mid143_contains root1_contains (c:=root143) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root144_contains : root144.Contains (rootPhase 144) := by
  have hh := CBox.mul_contains_e root72_contains root72_contains (c:=root144) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid145_contains : mid145.Contains (rootPhase 144) := root144_contains
lemma root145_contains : root145.Contains (rootPhase 145) := by
  have hh := CBox.mul_contains_e mid145_contains root1_contains (c:=root145) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root146_contains : root146.Contains (rootPhase 146) := by
  have hh := CBox.mul_contains_e root73_contains root73_contains (c:=root146) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid147_contains : mid147.Contains (rootPhase 146) := root146_contains
lemma root147_contains : root147.Contains (rootPhase 147) := by
  have hh := CBox.mul_contains_e mid147_contains root1_contains (c:=root147) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root148_contains : root148.Contains (rootPhase 148) := by
  have hh := CBox.mul_contains_e root74_contains root74_contains (c:=root148) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid149_contains : mid149.Contains (rootPhase 148) := root148_contains
lemma root149_contains : root149.Contains (rootPhase 149) := by
  have hh := CBox.mul_contains_e mid149_contains root1_contains (c:=root149) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root150_contains : root150.Contains (rootPhase 150) := by
  have hh := CBox.mul_contains_e root75_contains root75_contains (c:=root150) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid151_contains : mid151.Contains (rootPhase 150) := root150_contains
lemma root151_contains : root151.Contains (rootPhase 151) := by
  have hh := CBox.mul_contains_e mid151_contains root1_contains (c:=root151) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root152_contains : root152.Contains (rootPhase 152) := by
  have hh := CBox.mul_contains_e root76_contains root76_contains (c:=root152) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid153_contains : mid153.Contains (rootPhase 152) := root152_contains
lemma root153_contains : root153.Contains (rootPhase 153) := by
  have hh := CBox.mul_contains_e mid153_contains root1_contains (c:=root153) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root154_contains : root154.Contains (rootPhase 154) := by
  have hh := CBox.mul_contains_e root77_contains root77_contains (c:=root154) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid155_contains : mid155.Contains (rootPhase 154) := root154_contains
lemma root155_contains : root155.Contains (rootPhase 155) := by
  have hh := CBox.mul_contains_e mid155_contains root1_contains (c:=root155) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root156_contains : root156.Contains (rootPhase 156) := by
  have hh := CBox.mul_contains_e root78_contains root78_contains (c:=root156) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid157_contains : mid157.Contains (rootPhase 156) := root156_contains
lemma root157_contains : root157.Contains (rootPhase 157) := by
  have hh := CBox.mul_contains_e mid157_contains root1_contains (c:=root157) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root158_contains : root158.Contains (rootPhase 158) := by
  have hh := CBox.mul_contains_e root79_contains root79_contains (c:=root158) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid159_contains : mid159.Contains (rootPhase 158) := root158_contains
lemma root159_contains : root159.Contains (rootPhase 159) := by
  have hh := CBox.mul_contains_e mid159_contains root1_contains (c:=root159) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root160_contains : root160.Contains (rootPhase 160) := by
  have hh := CBox.mul_contains_e root80_contains root80_contains (c:=root160) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid161_contains : mid161.Contains (rootPhase 160) := root160_contains
lemma root161_contains : root161.Contains (rootPhase 161) := by
  have hh := CBox.mul_contains_e mid161_contains root1_contains (c:=root161) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root162_contains : root162.Contains (rootPhase 162) := by
  have hh := CBox.mul_contains_e root81_contains root81_contains (c:=root162) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid163_contains : mid163.Contains (rootPhase 162) := root162_contains
lemma root163_contains : root163.Contains (rootPhase 163) := by
  have hh := CBox.mul_contains_e mid163_contains root1_contains (c:=root163) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root164_contains : root164.Contains (rootPhase 164) := by
  have hh := CBox.mul_contains_e root82_contains root82_contains (c:=root164) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid165_contains : mid165.Contains (rootPhase 164) := root164_contains
lemma root165_contains : root165.Contains (rootPhase 165) := by
  have hh := CBox.mul_contains_e mid165_contains root1_contains (c:=root165) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root166_contains : root166.Contains (rootPhase 166) := by
  have hh := CBox.mul_contains_e root83_contains root83_contains (c:=root166) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid167_contains : mid167.Contains (rootPhase 166) := root166_contains
lemma root167_contains : root167.Contains (rootPhase 167) := by
  have hh := CBox.mul_contains_e mid167_contains root1_contains (c:=root167) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root168_contains : root168.Contains (rootPhase 168) := by
  have hh := CBox.mul_contains_e root84_contains root84_contains (c:=root168) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid169_contains : mid169.Contains (rootPhase 168) := root168_contains
lemma root169_contains : root169.Contains (rootPhase 169) := by
  have hh := CBox.mul_contains_e mid169_contains root1_contains (c:=root169) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root170_contains : root170.Contains (rootPhase 170) := by
  have hh := CBox.mul_contains_e root85_contains root85_contains (c:=root170) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid171_contains : mid171.Contains (rootPhase 170) := root170_contains
lemma root171_contains : root171.Contains (rootPhase 171) := by
  have hh := CBox.mul_contains_e mid171_contains root1_contains (c:=root171) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root172_contains : root172.Contains (rootPhase 172) := by
  have hh := CBox.mul_contains_e root86_contains root86_contains (c:=root172) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid173_contains : mid173.Contains (rootPhase 172) := root172_contains
lemma root173_contains : root173.Contains (rootPhase 173) := by
  have hh := CBox.mul_contains_e mid173_contains root1_contains (c:=root173) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root174_contains : root174.Contains (rootPhase 174) := by
  have hh := CBox.mul_contains_e root87_contains root87_contains (c:=root174) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid175_contains : mid175.Contains (rootPhase 174) := root174_contains
lemma root175_contains : root175.Contains (rootPhase 175) := by
  have hh := CBox.mul_contains_e mid175_contains root1_contains (c:=root175) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root176_contains : root176.Contains (rootPhase 176) := by
  have hh := CBox.mul_contains_e root88_contains root88_contains (c:=root176) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid177_contains : mid177.Contains (rootPhase 176) := root176_contains
lemma root177_contains : root177.Contains (rootPhase 177) := by
  have hh := CBox.mul_contains_e mid177_contains root1_contains (c:=root177) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root178_contains : root178.Contains (rootPhase 178) := by
  have hh := CBox.mul_contains_e root89_contains root89_contains (c:=root178) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid179_contains : mid179.Contains (rootPhase 178) := root178_contains
lemma root179_contains : root179.Contains (rootPhase 179) := by
  have hh := CBox.mul_contains_e mid179_contains root1_contains (c:=root179) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root180_contains : root180.Contains (rootPhase 180) := by
  have hh := CBox.mul_contains_e root90_contains root90_contains (c:=root180) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid181_contains : mid181.Contains (rootPhase 180) := root180_contains
lemma root181_contains : root181.Contains (rootPhase 181) := by
  have hh := CBox.mul_contains_e mid181_contains root1_contains (c:=root181) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root182_contains : root182.Contains (rootPhase 182) := by
  have hh := CBox.mul_contains_e root91_contains root91_contains (c:=root182) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid183_contains : mid183.Contains (rootPhase 182) := root182_contains
lemma root183_contains : root183.Contains (rootPhase 183) := by
  have hh := CBox.mul_contains_e mid183_contains root1_contains (c:=root183) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root184_contains : root184.Contains (rootPhase 184) := by
  have hh := CBox.mul_contains_e root92_contains root92_contains (c:=root184) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid185_contains : mid185.Contains (rootPhase 184) := root184_contains
lemma root185_contains : root185.Contains (rootPhase 185) := by
  have hh := CBox.mul_contains_e mid185_contains root1_contains (c:=root185) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root186_contains : root186.Contains (rootPhase 186) := by
  have hh := CBox.mul_contains_e root93_contains root93_contains (c:=root186) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid187_contains : mid187.Contains (rootPhase 186) := root186_contains
lemma root187_contains : root187.Contains (rootPhase 187) := by
  have hh := CBox.mul_contains_e mid187_contains root1_contains (c:=root187) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root188_contains : root188.Contains (rootPhase 188) := by
  have hh := CBox.mul_contains_e root94_contains root94_contains (c:=root188) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid189_contains : mid189.Contains (rootPhase 188) := root188_contains
lemma root189_contains : root189.Contains (rootPhase 189) := by
  have hh := CBox.mul_contains_e mid189_contains root1_contains (c:=root189) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root190_contains : root190.Contains (rootPhase 190) := by
  have hh := CBox.mul_contains_e root95_contains root95_contains (c:=root190) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid191_contains : mid191.Contains (rootPhase 190) := root190_contains
lemma root191_contains : root191.Contains (rootPhase 191) := by
  have hh := CBox.mul_contains_e mid191_contains root1_contains (c:=root191) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root192_contains : root192.Contains (rootPhase 192) := by
  have hh := CBox.mul_contains_e root96_contains root96_contains (c:=root192) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid193_contains : mid193.Contains (rootPhase 192) := root192_contains
lemma root193_contains : root193.Contains (rootPhase 193) := by
  have hh := CBox.mul_contains_e mid193_contains root1_contains (c:=root193) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root194_contains : root194.Contains (rootPhase 194) := by
  have hh := CBox.mul_contains_e root97_contains root97_contains (c:=root194) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid195_contains : mid195.Contains (rootPhase 194) := root194_contains
lemma root195_contains : root195.Contains (rootPhase 195) := by
  have hh := CBox.mul_contains_e mid195_contains root1_contains (c:=root195) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root196_contains : root196.Contains (rootPhase 196) := by
  have hh := CBox.mul_contains_e root98_contains root98_contains (c:=root196) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid197_contains : mid197.Contains (rootPhase 196) := root196_contains
lemma root197_contains : root197.Contains (rootPhase 197) := by
  have hh := CBox.mul_contains_e mid197_contains root1_contains (c:=root197) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root198_contains : root198.Contains (rootPhase 198) := by
  have hh := CBox.mul_contains_e root99_contains root99_contains (c:=root198) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid199_contains : mid199.Contains (rootPhase 198) := root198_contains
lemma root199_contains : root199.Contains (rootPhase 199) := by
  have hh := CBox.mul_contains_e mid199_contains root1_contains (c:=root199) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root200_contains : root200.Contains (rootPhase 200) := by
  have hh := CBox.mul_contains_e root100_contains root100_contains (c:=root200) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid201_contains : mid201.Contains (rootPhase 200) := root200_contains
lemma root201_contains : root201.Contains (rootPhase 201) := by
  have hh := CBox.mul_contains_e mid201_contains root1_contains (c:=root201) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root202_contains : root202.Contains (rootPhase 202) := by
  have hh := CBox.mul_contains_e root101_contains root101_contains (c:=root202) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid203_contains : mid203.Contains (rootPhase 202) := root202_contains
lemma root203_contains : root203.Contains (rootPhase 203) := by
  have hh := CBox.mul_contains_e mid203_contains root1_contains (c:=root203) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root204_contains : root204.Contains (rootPhase 204) := by
  have hh := CBox.mul_contains_e root102_contains root102_contains (c:=root204) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid205_contains : mid205.Contains (rootPhase 204) := root204_contains
lemma root205_contains : root205.Contains (rootPhase 205) := by
  have hh := CBox.mul_contains_e mid205_contains root1_contains (c:=root205) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root206_contains : root206.Contains (rootPhase 206) := by
  have hh := CBox.mul_contains_e root103_contains root103_contains (c:=root206) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid207_contains : mid207.Contains (rootPhase 206) := root206_contains
lemma root207_contains : root207.Contains (rootPhase 207) := by
  have hh := CBox.mul_contains_e mid207_contains root1_contains (c:=root207) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root208_contains : root208.Contains (rootPhase 208) := by
  have hh := CBox.mul_contains_e root104_contains root104_contains (c:=root208) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid209_contains : mid209.Contains (rootPhase 208) := root208_contains
lemma root209_contains : root209.Contains (rootPhase 209) := by
  have hh := CBox.mul_contains_e mid209_contains root1_contains (c:=root209) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root210_contains : root210.Contains (rootPhase 210) := by
  have hh := CBox.mul_contains_e root105_contains root105_contains (c:=root210) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid211_contains : mid211.Contains (rootPhase 210) := root210_contains
lemma root211_contains : root211.Contains (rootPhase 211) := by
  have hh := CBox.mul_contains_e mid211_contains root1_contains (c:=root211) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root212_contains : root212.Contains (rootPhase 212) := by
  have hh := CBox.mul_contains_e root106_contains root106_contains (c:=root212) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid213_contains : mid213.Contains (rootPhase 212) := root212_contains
lemma root213_contains : root213.Contains (rootPhase 213) := by
  have hh := CBox.mul_contains_e mid213_contains root1_contains (c:=root213) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root214_contains : root214.Contains (rootPhase 214) := by
  have hh := CBox.mul_contains_e root107_contains root107_contains (c:=root214) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid215_contains : mid215.Contains (rootPhase 214) := root214_contains
lemma root215_contains : root215.Contains (rootPhase 215) := by
  have hh := CBox.mul_contains_e mid215_contains root1_contains (c:=root215) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root216_contains : root216.Contains (rootPhase 216) := by
  have hh := CBox.mul_contains_e root108_contains root108_contains (c:=root216) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid217_contains : mid217.Contains (rootPhase 216) := root216_contains
lemma root217_contains : root217.Contains (rootPhase 217) := by
  have hh := CBox.mul_contains_e mid217_contains root1_contains (c:=root217) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root218_contains : root218.Contains (rootPhase 218) := by
  have hh := CBox.mul_contains_e root109_contains root109_contains (c:=root218) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid219_contains : mid219.Contains (rootPhase 218) := root218_contains
lemma root219_contains : root219.Contains (rootPhase 219) := by
  have hh := CBox.mul_contains_e mid219_contains root1_contains (c:=root219) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root220_contains : root220.Contains (rootPhase 220) := by
  have hh := CBox.mul_contains_e root110_contains root110_contains (c:=root220) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid221_contains : mid221.Contains (rootPhase 220) := root220_contains
lemma root221_contains : root221.Contains (rootPhase 221) := by
  have hh := CBox.mul_contains_e mid221_contains root1_contains (c:=root221) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root222_contains : root222.Contains (rootPhase 222) := by
  have hh := CBox.mul_contains_e root111_contains root111_contains (c:=root222) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid223_contains : mid223.Contains (rootPhase 222) := root222_contains
lemma root223_contains : root223.Contains (rootPhase 223) := by
  have hh := CBox.mul_contains_e mid223_contains root1_contains (c:=root223) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root224_contains : root224.Contains (rootPhase 224) := by
  have hh := CBox.mul_contains_e root112_contains root112_contains (c:=root224) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid225_contains : mid225.Contains (rootPhase 224) := root224_contains
lemma root225_contains : root225.Contains (rootPhase 225) := by
  have hh := CBox.mul_contains_e mid225_contains root1_contains (c:=root225) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root226_contains : root226.Contains (rootPhase 226) := by
  have hh := CBox.mul_contains_e root113_contains root113_contains (c:=root226) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid227_contains : mid227.Contains (rootPhase 226) := root226_contains
lemma root227_contains : root227.Contains (rootPhase 227) := by
  have hh := CBox.mul_contains_e mid227_contains root1_contains (c:=root227) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root228_contains : root228.Contains (rootPhase 228) := by
  have hh := CBox.mul_contains_e root114_contains root114_contains (c:=root228) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid229_contains : mid229.Contains (rootPhase 228) := root228_contains
lemma root229_contains : root229.Contains (rootPhase 229) := by
  have hh := CBox.mul_contains_e mid229_contains root1_contains (c:=root229) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root230_contains : root230.Contains (rootPhase 230) := by
  have hh := CBox.mul_contains_e root115_contains root115_contains (c:=root230) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid231_contains : mid231.Contains (rootPhase 230) := root230_contains
lemma root231_contains : root231.Contains (rootPhase 231) := by
  have hh := CBox.mul_contains_e mid231_contains root1_contains (c:=root231) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root232_contains : root232.Contains (rootPhase 232) := by
  have hh := CBox.mul_contains_e root116_contains root116_contains (c:=root232) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid233_contains : mid233.Contains (rootPhase 232) := root232_contains
lemma root233_contains : root233.Contains (rootPhase 233) := by
  have hh := CBox.mul_contains_e mid233_contains root1_contains (c:=root233) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root234_contains : root234.Contains (rootPhase 234) := by
  have hh := CBox.mul_contains_e root117_contains root117_contains (c:=root234) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid235_contains : mid235.Contains (rootPhase 234) := root234_contains
lemma root235_contains : root235.Contains (rootPhase 235) := by
  have hh := CBox.mul_contains_e mid235_contains root1_contains (c:=root235) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root236_contains : root236.Contains (rootPhase 236) := by
  have hh := CBox.mul_contains_e root118_contains root118_contains (c:=root236) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid237_contains : mid237.Contains (rootPhase 236) := root236_contains
lemma root237_contains : root237.Contains (rootPhase 237) := by
  have hh := CBox.mul_contains_e mid237_contains root1_contains (c:=root237) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root238_contains : root238.Contains (rootPhase 238) := by
  have hh := CBox.mul_contains_e root119_contains root119_contains (c:=root238) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid239_contains : mid239.Contains (rootPhase 238) := root238_contains
lemma root239_contains : root239.Contains (rootPhase 239) := by
  have hh := CBox.mul_contains_e mid239_contains root1_contains (c:=root239) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root240_contains : root240.Contains (rootPhase 240) := by
  have hh := CBox.mul_contains_e root120_contains root120_contains (c:=root240) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid241_contains : mid241.Contains (rootPhase 240) := root240_contains
lemma root241_contains : root241.Contains (rootPhase 241) := by
  have hh := CBox.mul_contains_e mid241_contains root1_contains (c:=root241) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root242_contains : root242.Contains (rootPhase 242) := by
  have hh := CBox.mul_contains_e root121_contains root121_contains (c:=root242) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid243_contains : mid243.Contains (rootPhase 242) := root242_contains
lemma root243_contains : root243.Contains (rootPhase 243) := by
  have hh := CBox.mul_contains_e mid243_contains root1_contains (c:=root243) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root244_contains : root244.Contains (rootPhase 244) := by
  have hh := CBox.mul_contains_e root122_contains root122_contains (c:=root244) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid245_contains : mid245.Contains (rootPhase 244) := root244_contains
lemma root245_contains : root245.Contains (rootPhase 245) := by
  have hh := CBox.mul_contains_e mid245_contains root1_contains (c:=root245) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root246_contains : root246.Contains (rootPhase 246) := by
  have hh := CBox.mul_contains_e root123_contains root123_contains (c:=root246) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid247_contains : mid247.Contains (rootPhase 246) := root246_contains
lemma root247_contains : root247.Contains (rootPhase 247) := by
  have hh := CBox.mul_contains_e mid247_contains root1_contains (c:=root247) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root248_contains : root248.Contains (rootPhase 248) := by
  have hh := CBox.mul_contains_e root124_contains root124_contains (c:=root248) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid249_contains : mid249.Contains (rootPhase 248) := root248_contains
lemma root249_contains : root249.Contains (rootPhase 249) := by
  have hh := CBox.mul_contains_e mid249_contains root1_contains (c:=root249) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root250_contains : root250.Contains (rootPhase 250) := by
  have hh := CBox.mul_contains_e root125_contains root125_contains (c:=root250) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid251_contains : mid251.Contains (rootPhase 250) := root250_contains
lemma root251_contains : root251.Contains (rootPhase 251) := by
  have hh := CBox.mul_contains_e mid251_contains root1_contains (c:=root251) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root252_contains : root252.Contains (rootPhase 252) := by
  have hh := CBox.mul_contains_e root126_contains root126_contains (c:=root252) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid253_contains : mid253.Contains (rootPhase 252) := root252_contains
lemma root253_contains : root253.Contains (rootPhase 253) := by
  have hh := CBox.mul_contains_e mid253_contains root1_contains (c:=root253) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root254_contains : root254.Contains (rootPhase 254) := by
  have hh := CBox.mul_contains_e root127_contains root127_contains (c:=root254) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid255_contains : mid255.Contains (rootPhase 254) := root254_contains
lemma root255_contains : root255.Contains (rootPhase 255) := by
  have hh := CBox.mul_contains_e mid255_contains root1_contains (c:=root255) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root256_contains : root256.Contains (rootPhase 256) := by
  have hh := CBox.mul_contains_e root128_contains root128_contains (c:=root256) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid257_contains : mid257.Contains (rootPhase 256) := root256_contains
lemma root257_contains : root257.Contains (rootPhase 257) := by
  have hh := CBox.mul_contains_e mid257_contains root1_contains (c:=root257) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root258_contains : root258.Contains (rootPhase 258) := by
  have hh := CBox.mul_contains_e root129_contains root129_contains (c:=root258) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid259_contains : mid259.Contains (rootPhase 258) := root258_contains
lemma root259_contains : root259.Contains (rootPhase 259) := by
  have hh := CBox.mul_contains_e mid259_contains root1_contains (c:=root259) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root260_contains : root260.Contains (rootPhase 260) := by
  have hh := CBox.mul_contains_e root130_contains root130_contains (c:=root260) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid261_contains : mid261.Contains (rootPhase 260) := root260_contains
lemma root261_contains : root261.Contains (rootPhase 261) := by
  have hh := CBox.mul_contains_e mid261_contains root1_contains (c:=root261) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root262_contains : root262.Contains (rootPhase 262) := by
  have hh := CBox.mul_contains_e root131_contains root131_contains (c:=root262) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid263_contains : mid263.Contains (rootPhase 262) := root262_contains
lemma root263_contains : root263.Contains (rootPhase 263) := by
  have hh := CBox.mul_contains_e mid263_contains root1_contains (c:=root263) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root264_contains : root264.Contains (rootPhase 264) := by
  have hh := CBox.mul_contains_e root132_contains root132_contains (c:=root264) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid265_contains : mid265.Contains (rootPhase 264) := root264_contains
lemma root265_contains : root265.Contains (rootPhase 265) := by
  have hh := CBox.mul_contains_e mid265_contains root1_contains (c:=root265) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root266_contains : root266.Contains (rootPhase 266) := by
  have hh := CBox.mul_contains_e root133_contains root133_contains (c:=root266) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid267_contains : mid267.Contains (rootPhase 266) := root266_contains
lemma root267_contains : root267.Contains (rootPhase 267) := by
  have hh := CBox.mul_contains_e mid267_contains root1_contains (c:=root267) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root268_contains : root268.Contains (rootPhase 268) := by
  have hh := CBox.mul_contains_e root134_contains root134_contains (c:=root268) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid269_contains : mid269.Contains (rootPhase 268) := root268_contains
lemma root269_contains : root269.Contains (rootPhase 269) := by
  have hh := CBox.mul_contains_e mid269_contains root1_contains (c:=root269) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root270_contains : root270.Contains (rootPhase 270) := by
  have hh := CBox.mul_contains_e root135_contains root135_contains (c:=root270) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid271_contains : mid271.Contains (rootPhase 270) := root270_contains
lemma root271_contains : root271.Contains (rootPhase 271) := by
  have hh := CBox.mul_contains_e mid271_contains root1_contains (c:=root271) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root272_contains : root272.Contains (rootPhase 272) := by
  have hh := CBox.mul_contains_e root136_contains root136_contains (c:=root272) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid273_contains : mid273.Contains (rootPhase 272) := root272_contains
lemma root273_contains : root273.Contains (rootPhase 273) := by
  have hh := CBox.mul_contains_e mid273_contains root1_contains (c:=root273) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root274_contains : root274.Contains (rootPhase 274) := by
  have hh := CBox.mul_contains_e root137_contains root137_contains (c:=root274) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid275_contains : mid275.Contains (rootPhase 274) := root274_contains
lemma root275_contains : root275.Contains (rootPhase 275) := by
  have hh := CBox.mul_contains_e mid275_contains root1_contains (c:=root275) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root276_contains : root276.Contains (rootPhase 276) := by
  have hh := CBox.mul_contains_e root138_contains root138_contains (c:=root276) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid277_contains : mid277.Contains (rootPhase 276) := root276_contains
lemma root277_contains : root277.Contains (rootPhase 277) := by
  have hh := CBox.mul_contains_e mid277_contains root1_contains (c:=root277) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root278_contains : root278.Contains (rootPhase 278) := by
  have hh := CBox.mul_contains_e root139_contains root139_contains (c:=root278) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid279_contains : mid279.Contains (rootPhase 278) := root278_contains
lemma root279_contains : root279.Contains (rootPhase 279) := by
  have hh := CBox.mul_contains_e mid279_contains root1_contains (c:=root279) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root280_contains : root280.Contains (rootPhase 280) := by
  have hh := CBox.mul_contains_e root140_contains root140_contains (c:=root280) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid281_contains : mid281.Contains (rootPhase 280) := root280_contains
lemma root281_contains : root281.Contains (rootPhase 281) := by
  have hh := CBox.mul_contains_e mid281_contains root1_contains (c:=root281) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root282_contains : root282.Contains (rootPhase 282) := by
  have hh := CBox.mul_contains_e root141_contains root141_contains (c:=root282) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid283_contains : mid283.Contains (rootPhase 282) := root282_contains
lemma root283_contains : root283.Contains (rootPhase 283) := by
  have hh := CBox.mul_contains_e mid283_contains root1_contains (c:=root283) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root284_contains : root284.Contains (rootPhase 284) := by
  have hh := CBox.mul_contains_e root142_contains root142_contains (c:=root284) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid285_contains : mid285.Contains (rootPhase 284) := root284_contains
lemma root285_contains : root285.Contains (rootPhase 285) := by
  have hh := CBox.mul_contains_e mid285_contains root1_contains (c:=root285) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root286_contains : root286.Contains (rootPhase 286) := by
  have hh := CBox.mul_contains_e root143_contains root143_contains (c:=root286) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid287_contains : mid287.Contains (rootPhase 286) := root286_contains
lemma root287_contains : root287.Contains (rootPhase 287) := by
  have hh := CBox.mul_contains_e mid287_contains root1_contains (c:=root287) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root288_contains : root288.Contains (rootPhase 288) := by
  have hh := CBox.mul_contains_e root144_contains root144_contains (c:=root288) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid289_contains : mid289.Contains (rootPhase 288) := root288_contains
lemma root289_contains : root289.Contains (rootPhase 289) := by
  have hh := CBox.mul_contains_e mid289_contains root1_contains (c:=root289) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root290_contains : root290.Contains (rootPhase 290) := by
  have hh := CBox.mul_contains_e root145_contains root145_contains (c:=root290) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid291_contains : mid291.Contains (rootPhase 290) := root290_contains
lemma root291_contains : root291.Contains (rootPhase 291) := by
  have hh := CBox.mul_contains_e mid291_contains root1_contains (c:=root291) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root292_contains : root292.Contains (rootPhase 292) := by
  have hh := CBox.mul_contains_e root146_contains root146_contains (c:=root292) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid293_contains : mid293.Contains (rootPhase 292) := root292_contains
lemma root293_contains : root293.Contains (rootPhase 293) := by
  have hh := CBox.mul_contains_e mid293_contains root1_contains (c:=root293) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root294_contains : root294.Contains (rootPhase 294) := by
  have hh := CBox.mul_contains_e root147_contains root147_contains (c:=root294) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid295_contains : mid295.Contains (rootPhase 294) := root294_contains
lemma root295_contains : root295.Contains (rootPhase 295) := by
  have hh := CBox.mul_contains_e mid295_contains root1_contains (c:=root295) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root296_contains : root296.Contains (rootPhase 296) := by
  have hh := CBox.mul_contains_e root148_contains root148_contains (c:=root296) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid297_contains : mid297.Contains (rootPhase 296) := root296_contains
lemma root297_contains : root297.Contains (rootPhase 297) := by
  have hh := CBox.mul_contains_e mid297_contains root1_contains (c:=root297) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root298_contains : root298.Contains (rootPhase 298) := by
  have hh := CBox.mul_contains_e root149_contains root149_contains (c:=root298) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid299_contains : mid299.Contains (rootPhase 298) := root298_contains
lemma root299_contains : root299.Contains (rootPhase 299) := by
  have hh := CBox.mul_contains_e mid299_contains root1_contains (c:=root299) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root300_contains : root300.Contains (rootPhase 300) := by
  have hh := CBox.mul_contains_e root150_contains root150_contains (c:=root300) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid301_contains : mid301.Contains (rootPhase 300) := root300_contains
lemma root301_contains : root301.Contains (rootPhase 301) := by
  have hh := CBox.mul_contains_e mid301_contains root1_contains (c:=root301) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root302_contains : root302.Contains (rootPhase 302) := by
  have hh := CBox.mul_contains_e root151_contains root151_contains (c:=root302) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid303_contains : mid303.Contains (rootPhase 302) := root302_contains
lemma root303_contains : root303.Contains (rootPhase 303) := by
  have hh := CBox.mul_contains_e mid303_contains root1_contains (c:=root303) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root304_contains : root304.Contains (rootPhase 304) := by
  have hh := CBox.mul_contains_e root152_contains root152_contains (c:=root304) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid305_contains : mid305.Contains (rootPhase 304) := root304_contains
lemma root305_contains : root305.Contains (rootPhase 305) := by
  have hh := CBox.mul_contains_e mid305_contains root1_contains (c:=root305) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root306_contains : root306.Contains (rootPhase 306) := by
  have hh := CBox.mul_contains_e root153_contains root153_contains (c:=root306) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid307_contains : mid307.Contains (rootPhase 306) := root306_contains
lemma root307_contains : root307.Contains (rootPhase 307) := by
  have hh := CBox.mul_contains_e mid307_contains root1_contains (c:=root307) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root308_contains : root308.Contains (rootPhase 308) := by
  have hh := CBox.mul_contains_e root154_contains root154_contains (c:=root308) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid309_contains : mid309.Contains (rootPhase 308) := root308_contains
lemma root309_contains : root309.Contains (rootPhase 309) := by
  have hh := CBox.mul_contains_e mid309_contains root1_contains (c:=root309) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root310_contains : root310.Contains (rootPhase 310) := by
  have hh := CBox.mul_contains_e root155_contains root155_contains (c:=root310) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid311_contains : mid311.Contains (rootPhase 310) := root310_contains
lemma root311_contains : root311.Contains (rootPhase 311) := by
  have hh := CBox.mul_contains_e mid311_contains root1_contains (c:=root311) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root312_contains : root312.Contains (rootPhase 312) := by
  have hh := CBox.mul_contains_e root156_contains root156_contains (c:=root312) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid313_contains : mid313.Contains (rootPhase 312) := root312_contains
lemma root313_contains : root313.Contains (rootPhase 313) := by
  have hh := CBox.mul_contains_e mid313_contains root1_contains (c:=root313) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root314_contains : root314.Contains (rootPhase 314) := by
  have hh := CBox.mul_contains_e root157_contains root157_contains (c:=root314) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid315_contains : mid315.Contains (rootPhase 314) := root314_contains
lemma root315_contains : root315.Contains (rootPhase 315) := by
  have hh := CBox.mul_contains_e mid315_contains root1_contains (c:=root315) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root316_contains : root316.Contains (rootPhase 316) := by
  have hh := CBox.mul_contains_e root158_contains root158_contains (c:=root316) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid317_contains : mid317.Contains (rootPhase 316) := root316_contains
lemma root317_contains : root317.Contains (rootPhase 317) := by
  have hh := CBox.mul_contains_e mid317_contains root1_contains (c:=root317) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root318_contains : root318.Contains (rootPhase 318) := by
  have hh := CBox.mul_contains_e root159_contains root159_contains (c:=root318) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid319_contains : mid319.Contains (rootPhase 318) := root318_contains
lemma root319_contains : root319.Contains (rootPhase 319) := by
  have hh := CBox.mul_contains_e mid319_contains root1_contains (c:=root319) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root320_contains : root320.Contains (rootPhase 320) := by
  have hh := CBox.mul_contains_e root160_contains root160_contains (c:=root320) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid321_contains : mid321.Contains (rootPhase 320) := root320_contains
lemma root321_contains : root321.Contains (rootPhase 321) := by
  have hh := CBox.mul_contains_e mid321_contains root1_contains (c:=root321) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root322_contains : root322.Contains (rootPhase 322) := by
  have hh := CBox.mul_contains_e root161_contains root161_contains (c:=root322) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid323_contains : mid323.Contains (rootPhase 322) := root322_contains
lemma root323_contains : root323.Contains (rootPhase 323) := by
  have hh := CBox.mul_contains_e mid323_contains root1_contains (c:=root323) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root324_contains : root324.Contains (rootPhase 324) := by
  have hh := CBox.mul_contains_e root162_contains root162_contains (c:=root324) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid325_contains : mid325.Contains (rootPhase 324) := root324_contains
lemma root325_contains : root325.Contains (rootPhase 325) := by
  have hh := CBox.mul_contains_e mid325_contains root1_contains (c:=root325) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root326_contains : root326.Contains (rootPhase 326) := by
  have hh := CBox.mul_contains_e root163_contains root163_contains (c:=root326) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid327_contains : mid327.Contains (rootPhase 326) := root326_contains
lemma root327_contains : root327.Contains (rootPhase 327) := by
  have hh := CBox.mul_contains_e mid327_contains root1_contains (c:=root327) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root328_contains : root328.Contains (rootPhase 328) := by
  have hh := CBox.mul_contains_e root164_contains root164_contains (c:=root328) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid329_contains : mid329.Contains (rootPhase 328) := root328_contains
lemma root329_contains : root329.Contains (rootPhase 329) := by
  have hh := CBox.mul_contains_e mid329_contains root1_contains (c:=root329) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root330_contains : root330.Contains (rootPhase 330) := by
  have hh := CBox.mul_contains_e root165_contains root165_contains (c:=root330) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid331_contains : mid331.Contains (rootPhase 330) := root330_contains
lemma root331_contains : root331.Contains (rootPhase 331) := by
  have hh := CBox.mul_contains_e mid331_contains root1_contains (c:=root331) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root332_contains : root332.Contains (rootPhase 332) := by
  have hh := CBox.mul_contains_e root166_contains root166_contains (c:=root332) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid333_contains : mid333.Contains (rootPhase 332) := root332_contains
lemma root333_contains : root333.Contains (rootPhase 333) := by
  have hh := CBox.mul_contains_e mid333_contains root1_contains (c:=root333) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root334_contains : root334.Contains (rootPhase 334) := by
  have hh := CBox.mul_contains_e root167_contains root167_contains (c:=root334) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid335_contains : mid335.Contains (rootPhase 334) := root334_contains
lemma root335_contains : root335.Contains (rootPhase 335) := by
  have hh := CBox.mul_contains_e mid335_contains root1_contains (c:=root335) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root336_contains : root336.Contains (rootPhase 336) := by
  have hh := CBox.mul_contains_e root168_contains root168_contains (c:=root336) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid337_contains : mid337.Contains (rootPhase 336) := root336_contains
lemma root337_contains : root337.Contains (rootPhase 337) := by
  have hh := CBox.mul_contains_e mid337_contains root1_contains (c:=root337) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root338_contains : root338.Contains (rootPhase 338) := by
  have hh := CBox.mul_contains_e root169_contains root169_contains (c:=root338) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid339_contains : mid339.Contains (rootPhase 338) := root338_contains
lemma root339_contains : root339.Contains (rootPhase 339) := by
  have hh := CBox.mul_contains_e mid339_contains root1_contains (c:=root339) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root340_contains : root340.Contains (rootPhase 340) := by
  have hh := CBox.mul_contains_e root170_contains root170_contains (c:=root340) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid341_contains : mid341.Contains (rootPhase 340) := root340_contains
lemma root341_contains : root341.Contains (rootPhase 341) := by
  have hh := CBox.mul_contains_e mid341_contains root1_contains (c:=root341) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root342_contains : root342.Contains (rootPhase 342) := by
  have hh := CBox.mul_contains_e root171_contains root171_contains (c:=root342) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid343_contains : mid343.Contains (rootPhase 342) := root342_contains
lemma root343_contains : root343.Contains (rootPhase 343) := by
  have hh := CBox.mul_contains_e mid343_contains root1_contains (c:=root343) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root344_contains : root344.Contains (rootPhase 344) := by
  have hh := CBox.mul_contains_e root172_contains root172_contains (c:=root344) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid345_contains : mid345.Contains (rootPhase 344) := root344_contains
lemma root345_contains : root345.Contains (rootPhase 345) := by
  have hh := CBox.mul_contains_e mid345_contains root1_contains (c:=root345) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root346_contains : root346.Contains (rootPhase 346) := by
  have hh := CBox.mul_contains_e root173_contains root173_contains (c:=root346) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid347_contains : mid347.Contains (rootPhase 346) := root346_contains
lemma root347_contains : root347.Contains (rootPhase 347) := by
  have hh := CBox.mul_contains_e mid347_contains root1_contains (c:=root347) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root348_contains : root348.Contains (rootPhase 348) := by
  have hh := CBox.mul_contains_e root174_contains root174_contains (c:=root348) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid349_contains : mid349.Contains (rootPhase 348) := root348_contains
lemma root349_contains : root349.Contains (rootPhase 349) := by
  have hh := CBox.mul_contains_e mid349_contains root1_contains (c:=root349) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root350_contains : root350.Contains (rootPhase 350) := by
  have hh := CBox.mul_contains_e root175_contains root175_contains (c:=root350) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid351_contains : mid351.Contains (rootPhase 350) := root350_contains
lemma root351_contains : root351.Contains (rootPhase 351) := by
  have hh := CBox.mul_contains_e mid351_contains root1_contains (c:=root351) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root352_contains : root352.Contains (rootPhase 352) := by
  have hh := CBox.mul_contains_e root176_contains root176_contains (c:=root352) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid353_contains : mid353.Contains (rootPhase 352) := root352_contains
lemma root353_contains : root353.Contains (rootPhase 353) := by
  have hh := CBox.mul_contains_e mid353_contains root1_contains (c:=root353) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root354_contains : root354.Contains (rootPhase 354) := by
  have hh := CBox.mul_contains_e root177_contains root177_contains (c:=root354) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid355_contains : mid355.Contains (rootPhase 354) := root354_contains
lemma root355_contains : root355.Contains (rootPhase 355) := by
  have hh := CBox.mul_contains_e mid355_contains root1_contains (c:=root355) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root356_contains : root356.Contains (rootPhase 356) := by
  have hh := CBox.mul_contains_e root178_contains root178_contains (c:=root356) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid357_contains : mid357.Contains (rootPhase 356) := root356_contains
lemma root357_contains : root357.Contains (rootPhase 357) := by
  have hh := CBox.mul_contains_e mid357_contains root1_contains (c:=root357) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root358_contains : root358.Contains (rootPhase 358) := by
  have hh := CBox.mul_contains_e root179_contains root179_contains (c:=root358) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid359_contains : mid359.Contains (rootPhase 358) := root358_contains
lemma root359_contains : root359.Contains (rootPhase 359) := by
  have hh := CBox.mul_contains_e mid359_contains root1_contains (c:=root359) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root360_contains : root360.Contains (rootPhase 360) := by
  have hh := CBox.mul_contains_e root180_contains root180_contains (c:=root360) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid361_contains : mid361.Contains (rootPhase 360) := root360_contains
lemma root361_contains : root361.Contains (rootPhase 361) := by
  have hh := CBox.mul_contains_e mid361_contains root1_contains (c:=root361) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root362_contains : root362.Contains (rootPhase 362) := by
  have hh := CBox.mul_contains_e root181_contains root181_contains (c:=root362) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid363_contains : mid363.Contains (rootPhase 362) := root362_contains
lemma root363_contains : root363.Contains (rootPhase 363) := by
  have hh := CBox.mul_contains_e mid363_contains root1_contains (c:=root363) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root364_contains : root364.Contains (rootPhase 364) := by
  have hh := CBox.mul_contains_e root182_contains root182_contains (c:=root364) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid365_contains : mid365.Contains (rootPhase 364) := root364_contains
lemma root365_contains : root365.Contains (rootPhase 365) := by
  have hh := CBox.mul_contains_e mid365_contains root1_contains (c:=root365) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root366_contains : root366.Contains (rootPhase 366) := by
  have hh := CBox.mul_contains_e root183_contains root183_contains (c:=root366) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid367_contains : mid367.Contains (rootPhase 366) := root366_contains
lemma root367_contains : root367.Contains (rootPhase 367) := by
  have hh := CBox.mul_contains_e mid367_contains root1_contains (c:=root367) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root368_contains : root368.Contains (rootPhase 368) := by
  have hh := CBox.mul_contains_e root184_contains root184_contains (c:=root368) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid369_contains : mid369.Contains (rootPhase 368) := root368_contains
lemma root369_contains : root369.Contains (rootPhase 369) := by
  have hh := CBox.mul_contains_e mid369_contains root1_contains (c:=root369) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root370_contains : root370.Contains (rootPhase 370) := by
  have hh := CBox.mul_contains_e root185_contains root185_contains (c:=root370) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid371_contains : mid371.Contains (rootPhase 370) := root370_contains
lemma root371_contains : root371.Contains (rootPhase 371) := by
  have hh := CBox.mul_contains_e mid371_contains root1_contains (c:=root371) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root372_contains : root372.Contains (rootPhase 372) := by
  have hh := CBox.mul_contains_e root186_contains root186_contains (c:=root372) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid373_contains : mid373.Contains (rootPhase 372) := root372_contains
lemma root373_contains : root373.Contains (rootPhase 373) := by
  have hh := CBox.mul_contains_e mid373_contains root1_contains (c:=root373) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root374_contains : root374.Contains (rootPhase 374) := by
  have hh := CBox.mul_contains_e root187_contains root187_contains (c:=root374) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid375_contains : mid375.Contains (rootPhase 374) := root374_contains
lemma root375_contains : root375.Contains (rootPhase 375) := by
  have hh := CBox.mul_contains_e mid375_contains root1_contains (c:=root375) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root376_contains : root376.Contains (rootPhase 376) := by
  have hh := CBox.mul_contains_e root188_contains root188_contains (c:=root376) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid377_contains : mid377.Contains (rootPhase 376) := root376_contains
lemma root377_contains : root377.Contains (rootPhase 377) := by
  have hh := CBox.mul_contains_e mid377_contains root1_contains (c:=root377) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root378_contains : root378.Contains (rootPhase 378) := by
  have hh := CBox.mul_contains_e root189_contains root189_contains (c:=root378) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid379_contains : mid379.Contains (rootPhase 378) := root378_contains
lemma root379_contains : root379.Contains (rootPhase 379) := by
  have hh := CBox.mul_contains_e mid379_contains root1_contains (c:=root379) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root380_contains : root380.Contains (rootPhase 380) := by
  have hh := CBox.mul_contains_e root190_contains root190_contains (c:=root380) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid381_contains : mid381.Contains (rootPhase 380) := root380_contains
lemma root381_contains : root381.Contains (rootPhase 381) := by
  have hh := CBox.mul_contains_e mid381_contains root1_contains (c:=root381) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root382_contains : root382.Contains (rootPhase 382) := by
  have hh := CBox.mul_contains_e root191_contains root191_contains (c:=root382) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid383_contains : mid383.Contains (rootPhase 382) := root382_contains
lemma root383_contains : root383.Contains (rootPhase 383) := by
  have hh := CBox.mul_contains_e mid383_contains root1_contains (c:=root383) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root384_contains : root384.Contains (rootPhase 384) := by
  have hh := CBox.mul_contains_e root192_contains root192_contains (c:=root384) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid385_contains : mid385.Contains (rootPhase 384) := root384_contains
lemma root385_contains : root385.Contains (rootPhase 385) := by
  have hh := CBox.mul_contains_e mid385_contains root1_contains (c:=root385) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root386_contains : root386.Contains (rootPhase 386) := by
  have hh := CBox.mul_contains_e root193_contains root193_contains (c:=root386) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid387_contains : mid387.Contains (rootPhase 386) := root386_contains
lemma root387_contains : root387.Contains (rootPhase 387) := by
  have hh := CBox.mul_contains_e mid387_contains root1_contains (c:=root387) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root388_contains : root388.Contains (rootPhase 388) := by
  have hh := CBox.mul_contains_e root194_contains root194_contains (c:=root388) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid389_contains : mid389.Contains (rootPhase 388) := root388_contains
lemma root389_contains : root389.Contains (rootPhase 389) := by
  have hh := CBox.mul_contains_e mid389_contains root1_contains (c:=root389) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root390_contains : root390.Contains (rootPhase 390) := by
  have hh := CBox.mul_contains_e root195_contains root195_contains (c:=root390) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid391_contains : mid391.Contains (rootPhase 390) := root390_contains
lemma root391_contains : root391.Contains (rootPhase 391) := by
  have hh := CBox.mul_contains_e mid391_contains root1_contains (c:=root391) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root392_contains : root392.Contains (rootPhase 392) := by
  have hh := CBox.mul_contains_e root196_contains root196_contains (c:=root392) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid393_contains : mid393.Contains (rootPhase 392) := root392_contains
lemma root393_contains : root393.Contains (rootPhase 393) := by
  have hh := CBox.mul_contains_e mid393_contains root1_contains (c:=root393) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root394_contains : root394.Contains (rootPhase 394) := by
  have hh := CBox.mul_contains_e root197_contains root197_contains (c:=root394) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid395_contains : mid395.Contains (rootPhase 394) := root394_contains
lemma root395_contains : root395.Contains (rootPhase 395) := by
  have hh := CBox.mul_contains_e mid395_contains root1_contains (c:=root395) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root396_contains : root396.Contains (rootPhase 396) := by
  have hh := CBox.mul_contains_e root198_contains root198_contains (c:=root396) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid397_contains : mid397.Contains (rootPhase 396) := root396_contains
lemma root397_contains : root397.Contains (rootPhase 397) := by
  have hh := CBox.mul_contains_e mid397_contains root1_contains (c:=root397) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root398_contains : root398.Contains (rootPhase 398) := by
  have hh := CBox.mul_contains_e root199_contains root199_contains (c:=root398) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid399_contains : mid399.Contains (rootPhase 398) := root398_contains
lemma root399_contains : root399.Contains (rootPhase 399) := by
  have hh := CBox.mul_contains_e mid399_contains root1_contains (c:=root399) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root400_contains : root400.Contains (rootPhase 400) := by
  have hh := CBox.mul_contains_e root200_contains root200_contains (c:=root400) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid401_contains : mid401.Contains (rootPhase 400) := root400_contains
lemma root401_contains : root401.Contains (rootPhase 401) := by
  have hh := CBox.mul_contains_e mid401_contains root1_contains (c:=root401) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root402_contains : root402.Contains (rootPhase 402) := by
  have hh := CBox.mul_contains_e root201_contains root201_contains (c:=root402) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid403_contains : mid403.Contains (rootPhase 402) := root402_contains
lemma root403_contains : root403.Contains (rootPhase 403) := by
  have hh := CBox.mul_contains_e mid403_contains root1_contains (c:=root403) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root404_contains : root404.Contains (rootPhase 404) := by
  have hh := CBox.mul_contains_e root202_contains root202_contains (c:=root404) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid405_contains : mid405.Contains (rootPhase 404) := root404_contains
lemma root405_contains : root405.Contains (rootPhase 405) := by
  have hh := CBox.mul_contains_e mid405_contains root1_contains (c:=root405) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root406_contains : root406.Contains (rootPhase 406) := by
  have hh := CBox.mul_contains_e root203_contains root203_contains (c:=root406) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid407_contains : mid407.Contains (rootPhase 406) := root406_contains
lemma root407_contains : root407.Contains (rootPhase 407) := by
  have hh := CBox.mul_contains_e mid407_contains root1_contains (c:=root407) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root408_contains : root408.Contains (rootPhase 408) := by
  have hh := CBox.mul_contains_e root204_contains root204_contains (c:=root408) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid409_contains : mid409.Contains (rootPhase 408) := root408_contains
lemma root409_contains : root409.Contains (rootPhase 409) := by
  have hh := CBox.mul_contains_e mid409_contains root1_contains (c:=root409) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root410_contains : root410.Contains (rootPhase 410) := by
  have hh := CBox.mul_contains_e root205_contains root205_contains (c:=root410) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid411_contains : mid411.Contains (rootPhase 410) := root410_contains
lemma root411_contains : root411.Contains (rootPhase 411) := by
  have hh := CBox.mul_contains_e mid411_contains root1_contains (c:=root411) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root412_contains : root412.Contains (rootPhase 412) := by
  have hh := CBox.mul_contains_e root206_contains root206_contains (c:=root412) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid413_contains : mid413.Contains (rootPhase 412) := root412_contains
lemma root413_contains : root413.Contains (rootPhase 413) := by
  have hh := CBox.mul_contains_e mid413_contains root1_contains (c:=root413) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root414_contains : root414.Contains (rootPhase 414) := by
  have hh := CBox.mul_contains_e root207_contains root207_contains (c:=root414) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid415_contains : mid415.Contains (rootPhase 414) := root414_contains
lemma root415_contains : root415.Contains (rootPhase 415) := by
  have hh := CBox.mul_contains_e mid415_contains root1_contains (c:=root415) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root416_contains : root416.Contains (rootPhase 416) := by
  have hh := CBox.mul_contains_e root208_contains root208_contains (c:=root416) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid417_contains : mid417.Contains (rootPhase 416) := root416_contains
lemma root417_contains : root417.Contains (rootPhase 417) := by
  have hh := CBox.mul_contains_e mid417_contains root1_contains (c:=root417) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root418_contains : root418.Contains (rootPhase 418) := by
  have hh := CBox.mul_contains_e root209_contains root209_contains (c:=root418) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid419_contains : mid419.Contains (rootPhase 418) := root418_contains
lemma root419_contains : root419.Contains (rootPhase 419) := by
  have hh := CBox.mul_contains_e mid419_contains root1_contains (c:=root419) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root420_contains : root420.Contains (rootPhase 420) := by
  have hh := CBox.mul_contains_e root210_contains root210_contains (c:=root420) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid421_contains : mid421.Contains (rootPhase 420) := root420_contains
lemma root421_contains : root421.Contains (rootPhase 421) := by
  have hh := CBox.mul_contains_e mid421_contains root1_contains (c:=root421) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root422_contains : root422.Contains (rootPhase 422) := by
  have hh := CBox.mul_contains_e root211_contains root211_contains (c:=root422) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid423_contains : mid423.Contains (rootPhase 422) := root422_contains
lemma root423_contains : root423.Contains (rootPhase 423) := by
  have hh := CBox.mul_contains_e mid423_contains root1_contains (c:=root423) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root424_contains : root424.Contains (rootPhase 424) := by
  have hh := CBox.mul_contains_e root212_contains root212_contains (c:=root424) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid425_contains : mid425.Contains (rootPhase 424) := root424_contains
lemma root425_contains : root425.Contains (rootPhase 425) := by
  have hh := CBox.mul_contains_e mid425_contains root1_contains (c:=root425) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root426_contains : root426.Contains (rootPhase 426) := by
  have hh := CBox.mul_contains_e root213_contains root213_contains (c:=root426) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid427_contains : mid427.Contains (rootPhase 426) := root426_contains
lemma root427_contains : root427.Contains (rootPhase 427) := by
  have hh := CBox.mul_contains_e mid427_contains root1_contains (c:=root427) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root428_contains : root428.Contains (rootPhase 428) := by
  have hh := CBox.mul_contains_e root214_contains root214_contains (c:=root428) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid429_contains : mid429.Contains (rootPhase 428) := root428_contains
lemma root429_contains : root429.Contains (rootPhase 429) := by
  have hh := CBox.mul_contains_e mid429_contains root1_contains (c:=root429) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root430_contains : root430.Contains (rootPhase 430) := by
  have hh := CBox.mul_contains_e root215_contains root215_contains (c:=root430) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid431_contains : mid431.Contains (rootPhase 430) := root430_contains
lemma root431_contains : root431.Contains (rootPhase 431) := by
  have hh := CBox.mul_contains_e mid431_contains root1_contains (c:=root431) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root432_contains : root432.Contains (rootPhase 432) := by
  have hh := CBox.mul_contains_e root216_contains root216_contains (c:=root432) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid433_contains : mid433.Contains (rootPhase 432) := root432_contains
lemma root433_contains : root433.Contains (rootPhase 433) := by
  have hh := CBox.mul_contains_e mid433_contains root1_contains (c:=root433) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root434_contains : root434.Contains (rootPhase 434) := by
  have hh := CBox.mul_contains_e root217_contains root217_contains (c:=root434) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid435_contains : mid435.Contains (rootPhase 434) := root434_contains
lemma root435_contains : root435.Contains (rootPhase 435) := by
  have hh := CBox.mul_contains_e mid435_contains root1_contains (c:=root435) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root436_contains : root436.Contains (rootPhase 436) := by
  have hh := CBox.mul_contains_e root218_contains root218_contains (c:=root436) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid437_contains : mid437.Contains (rootPhase 436) := root436_contains
lemma root437_contains : root437.Contains (rootPhase 437) := by
  have hh := CBox.mul_contains_e mid437_contains root1_contains (c:=root437) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root438_contains : root438.Contains (rootPhase 438) := by
  have hh := CBox.mul_contains_e root219_contains root219_contains (c:=root438) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid439_contains : mid439.Contains (rootPhase 438) := root438_contains
lemma root439_contains : root439.Contains (rootPhase 439) := by
  have hh := CBox.mul_contains_e mid439_contains root1_contains (c:=root439) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root440_contains : root440.Contains (rootPhase 440) := by
  have hh := CBox.mul_contains_e root220_contains root220_contains (c:=root440) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid441_contains : mid441.Contains (rootPhase 440) := root440_contains
lemma root441_contains : root441.Contains (rootPhase 441) := by
  have hh := CBox.mul_contains_e mid441_contains root1_contains (c:=root441) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root442_contains : root442.Contains (rootPhase 442) := by
  have hh := CBox.mul_contains_e root221_contains root221_contains (c:=root442) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid443_contains : mid443.Contains (rootPhase 442) := root442_contains
lemma root443_contains : root443.Contains (rootPhase 443) := by
  have hh := CBox.mul_contains_e mid443_contains root1_contains (c:=root443) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root444_contains : root444.Contains (rootPhase 444) := by
  have hh := CBox.mul_contains_e root222_contains root222_contains (c:=root444) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid445_contains : mid445.Contains (rootPhase 444) := root444_contains
lemma root445_contains : root445.Contains (rootPhase 445) := by
  have hh := CBox.mul_contains_e mid445_contains root1_contains (c:=root445) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root446_contains : root446.Contains (rootPhase 446) := by
  have hh := CBox.mul_contains_e root223_contains root223_contains (c:=root446) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid447_contains : mid447.Contains (rootPhase 446) := root446_contains
lemma root447_contains : root447.Contains (rootPhase 447) := by
  have hh := CBox.mul_contains_e mid447_contains root1_contains (c:=root447) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root448_contains : root448.Contains (rootPhase 448) := by
  have hh := CBox.mul_contains_e root224_contains root224_contains (c:=root448) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid449_contains : mid449.Contains (rootPhase 448) := root448_contains
lemma root449_contains : root449.Contains (rootPhase 449) := by
  have hh := CBox.mul_contains_e mid449_contains root1_contains (c:=root449) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root450_contains : root450.Contains (rootPhase 450) := by
  have hh := CBox.mul_contains_e root225_contains root225_contains (c:=root450) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid451_contains : mid451.Contains (rootPhase 450) := root450_contains
lemma root451_contains : root451.Contains (rootPhase 451) := by
  have hh := CBox.mul_contains_e mid451_contains root1_contains (c:=root451) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root452_contains : root452.Contains (rootPhase 452) := by
  have hh := CBox.mul_contains_e root226_contains root226_contains (c:=root452) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid453_contains : mid453.Contains (rootPhase 452) := root452_contains
lemma root453_contains : root453.Contains (rootPhase 453) := by
  have hh := CBox.mul_contains_e mid453_contains root1_contains (c:=root453) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root454_contains : root454.Contains (rootPhase 454) := by
  have hh := CBox.mul_contains_e root227_contains root227_contains (c:=root454) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid455_contains : mid455.Contains (rootPhase 454) := root454_contains
lemma root455_contains : root455.Contains (rootPhase 455) := by
  have hh := CBox.mul_contains_e mid455_contains root1_contains (c:=root455) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root456_contains : root456.Contains (rootPhase 456) := by
  have hh := CBox.mul_contains_e root228_contains root228_contains (c:=root456) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid457_contains : mid457.Contains (rootPhase 456) := root456_contains
lemma root457_contains : root457.Contains (rootPhase 457) := by
  have hh := CBox.mul_contains_e mid457_contains root1_contains (c:=root457) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root458_contains : root458.Contains (rootPhase 458) := by
  have hh := CBox.mul_contains_e root229_contains root229_contains (c:=root458) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid459_contains : mid459.Contains (rootPhase 458) := root458_contains
lemma root459_contains : root459.Contains (rootPhase 459) := by
  have hh := CBox.mul_contains_e mid459_contains root1_contains (c:=root459) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root460_contains : root460.Contains (rootPhase 460) := by
  have hh := CBox.mul_contains_e root230_contains root230_contains (c:=root460) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid461_contains : mid461.Contains (rootPhase 460) := root460_contains
lemma root461_contains : root461.Contains (rootPhase 461) := by
  have hh := CBox.mul_contains_e mid461_contains root1_contains (c:=root461) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root462_contains : root462.Contains (rootPhase 462) := by
  have hh := CBox.mul_contains_e root231_contains root231_contains (c:=root462) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid463_contains : mid463.Contains (rootPhase 462) := root462_contains
lemma root463_contains : root463.Contains (rootPhase 463) := by
  have hh := CBox.mul_contains_e mid463_contains root1_contains (c:=root463) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root464_contains : root464.Contains (rootPhase 464) := by
  have hh := CBox.mul_contains_e root232_contains root232_contains (c:=root464) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid465_contains : mid465.Contains (rootPhase 464) := root464_contains
lemma root465_contains : root465.Contains (rootPhase 465) := by
  have hh := CBox.mul_contains_e mid465_contains root1_contains (c:=root465) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root466_contains : root466.Contains (rootPhase 466) := by
  have hh := CBox.mul_contains_e root233_contains root233_contains (c:=root466) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid467_contains : mid467.Contains (rootPhase 466) := root466_contains
lemma root467_contains : root467.Contains (rootPhase 467) := by
  have hh := CBox.mul_contains_e mid467_contains root1_contains (c:=root467) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root468_contains : root468.Contains (rootPhase 468) := by
  have hh := CBox.mul_contains_e root234_contains root234_contains (c:=root468) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid469_contains : mid469.Contains (rootPhase 468) := root468_contains
lemma root469_contains : root469.Contains (rootPhase 469) := by
  have hh := CBox.mul_contains_e mid469_contains root1_contains (c:=root469) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root470_contains : root470.Contains (rootPhase 470) := by
  have hh := CBox.mul_contains_e root235_contains root235_contains (c:=root470) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid471_contains : mid471.Contains (rootPhase 470) := root470_contains
lemma root471_contains : root471.Contains (rootPhase 471) := by
  have hh := CBox.mul_contains_e mid471_contains root1_contains (c:=root471) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root472_contains : root472.Contains (rootPhase 472) := by
  have hh := CBox.mul_contains_e root236_contains root236_contains (c:=root472) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid473_contains : mid473.Contains (rootPhase 472) := root472_contains
lemma root473_contains : root473.Contains (rootPhase 473) := by
  have hh := CBox.mul_contains_e mid473_contains root1_contains (c:=root473) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root474_contains : root474.Contains (rootPhase 474) := by
  have hh := CBox.mul_contains_e root237_contains root237_contains (c:=root474) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid475_contains : mid475.Contains (rootPhase 474) := root474_contains
lemma root475_contains : root475.Contains (rootPhase 475) := by
  have hh := CBox.mul_contains_e mid475_contains root1_contains (c:=root475) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root476_contains : root476.Contains (rootPhase 476) := by
  have hh := CBox.mul_contains_e root238_contains root238_contains (c:=root476) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid477_contains : mid477.Contains (rootPhase 476) := root476_contains
lemma root477_contains : root477.Contains (rootPhase 477) := by
  have hh := CBox.mul_contains_e mid477_contains root1_contains (c:=root477) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root478_contains : root478.Contains (rootPhase 478) := by
  have hh := CBox.mul_contains_e root239_contains root239_contains (c:=root478) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid479_contains : mid479.Contains (rootPhase 478) := root478_contains
lemma root479_contains : root479.Contains (rootPhase 479) := by
  have hh := CBox.mul_contains_e mid479_contains root1_contains (c:=root479) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root480_contains : root480.Contains (rootPhase 480) := by
  have hh := CBox.mul_contains_e root240_contains root240_contains (c:=root480) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid481_contains : mid481.Contains (rootPhase 480) := root480_contains
lemma root481_contains : root481.Contains (rootPhase 481) := by
  have hh := CBox.mul_contains_e mid481_contains root1_contains (c:=root481) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root482_contains : root482.Contains (rootPhase 482) := by
  have hh := CBox.mul_contains_e root241_contains root241_contains (c:=root482) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid483_contains : mid483.Contains (rootPhase 482) := root482_contains
lemma root483_contains : root483.Contains (rootPhase 483) := by
  have hh := CBox.mul_contains_e mid483_contains root1_contains (c:=root483) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root484_contains : root484.Contains (rootPhase 484) := by
  have hh := CBox.mul_contains_e root242_contains root242_contains (c:=root484) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid485_contains : mid485.Contains (rootPhase 484) := root484_contains
lemma root485_contains : root485.Contains (rootPhase 485) := by
  have hh := CBox.mul_contains_e mid485_contains root1_contains (c:=root485) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root486_contains : root486.Contains (rootPhase 486) := by
  have hh := CBox.mul_contains_e root243_contains root243_contains (c:=root486) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid487_contains : mid487.Contains (rootPhase 486) := root486_contains
lemma root487_contains : root487.Contains (rootPhase 487) := by
  have hh := CBox.mul_contains_e mid487_contains root1_contains (c:=root487) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root488_contains : root488.Contains (rootPhase 488) := by
  have hh := CBox.mul_contains_e root244_contains root244_contains (c:=root488) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid489_contains : mid489.Contains (rootPhase 488) := root488_contains
lemma root489_contains : root489.Contains (rootPhase 489) := by
  have hh := CBox.mul_contains_e mid489_contains root1_contains (c:=root489) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root490_contains : root490.Contains (rootPhase 490) := by
  have hh := CBox.mul_contains_e root245_contains root245_contains (c:=root490) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid491_contains : mid491.Contains (rootPhase 490) := root490_contains
lemma root491_contains : root491.Contains (rootPhase 491) := by
  have hh := CBox.mul_contains_e mid491_contains root1_contains (c:=root491) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root492_contains : root492.Contains (rootPhase 492) := by
  have hh := CBox.mul_contains_e root246_contains root246_contains (c:=root492) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid493_contains : mid493.Contains (rootPhase 492) := root492_contains
lemma root493_contains : root493.Contains (rootPhase 493) := by
  have hh := CBox.mul_contains_e mid493_contains root1_contains (c:=root493) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root494_contains : root494.Contains (rootPhase 494) := by
  have hh := CBox.mul_contains_e root247_contains root247_contains (c:=root494) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid495_contains : mid495.Contains (rootPhase 494) := root494_contains
lemma root495_contains : root495.Contains (rootPhase 495) := by
  have hh := CBox.mul_contains_e mid495_contains root1_contains (c:=root495) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root496_contains : root496.Contains (rootPhase 496) := by
  have hh := CBox.mul_contains_e root248_contains root248_contains (c:=root496) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid497_contains : mid497.Contains (rootPhase 496) := root496_contains
lemma root497_contains : root497.Contains (rootPhase 497) := by
  have hh := CBox.mul_contains_e mid497_contains root1_contains (c:=root497) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root498_contains : root498.Contains (rootPhase 498) := by
  have hh := CBox.mul_contains_e root249_contains root249_contains (c:=root498) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid499_contains : mid499.Contains (rootPhase 498) := root498_contains
lemma root499_contains : root499.Contains (rootPhase 499) := by
  have hh := CBox.mul_contains_e mid499_contains root1_contains (c:=root499) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root500_contains : root500.Contains (rootPhase 500) := by
  have hh := CBox.mul_contains_e root250_contains root250_contains (c:=root500) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid501_contains : mid501.Contains (rootPhase 500) := root500_contains
lemma root501_contains : root501.Contains (rootPhase 501) := by
  have hh := CBox.mul_contains_e mid501_contains root1_contains (c:=root501) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root502_contains : root502.Contains (rootPhase 502) := by
  have hh := CBox.mul_contains_e root251_contains root251_contains (c:=root502) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid503_contains : mid503.Contains (rootPhase 502) := root502_contains
lemma root503_contains : root503.Contains (rootPhase 503) := by
  have hh := CBox.mul_contains_e mid503_contains root1_contains (c:=root503) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root504_contains : root504.Contains (rootPhase 504) := by
  have hh := CBox.mul_contains_e root252_contains root252_contains (c:=root504) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid505_contains : mid505.Contains (rootPhase 504) := root504_contains
lemma root505_contains : root505.Contains (rootPhase 505) := by
  have hh := CBox.mul_contains_e mid505_contains root1_contains (c:=root505) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root506_contains : root506.Contains (rootPhase 506) := by
  have hh := CBox.mul_contains_e root253_contains root253_contains (c:=root506) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid507_contains : mid507.Contains (rootPhase 506) := root506_contains
lemma root507_contains : root507.Contains (rootPhase 507) := by
  have hh := CBox.mul_contains_e mid507_contains root1_contains (c:=root507) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root508_contains : root508.Contains (rootPhase 508) := by
  have hh := CBox.mul_contains_e root254_contains root254_contains (c:=root508) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid509_contains : mid509.Contains (rootPhase 508) := root508_contains
lemma root509_contains : root509.Contains (rootPhase 509) := by
  have hh := CBox.mul_contains_e mid509_contains root1_contains (c:=root509) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root510_contains : root510.Contains (rootPhase 510) := by
  have hh := CBox.mul_contains_e root255_contains root255_contains (c:=root510) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid511_contains : mid511.Contains (rootPhase 510) := root510_contains
lemma root511_contains : root511.Contains (rootPhase 511) := by
  have hh := CBox.mul_contains_e mid511_contains root1_contains (c:=root511) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root512_contains : root512.Contains (rootPhase 512) := by
  have hh := CBox.mul_contains_e root256_contains root256_contains (c:=root512) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid513_contains : mid513.Contains (rootPhase 512) := root512_contains
lemma root513_contains : root513.Contains (rootPhase 513) := by
  have hh := CBox.mul_contains_e mid513_contains root1_contains (c:=root513) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root514_contains : root514.Contains (rootPhase 514) := by
  have hh := CBox.mul_contains_e root257_contains root257_contains (c:=root514) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid515_contains : mid515.Contains (rootPhase 514) := root514_contains
lemma root515_contains : root515.Contains (rootPhase 515) := by
  have hh := CBox.mul_contains_e mid515_contains root1_contains (c:=root515) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root516_contains : root516.Contains (rootPhase 516) := by
  have hh := CBox.mul_contains_e root258_contains root258_contains (c:=root516) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid517_contains : mid517.Contains (rootPhase 516) := root516_contains
lemma root517_contains : root517.Contains (rootPhase 517) := by
  have hh := CBox.mul_contains_e mid517_contains root1_contains (c:=root517) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root518_contains : root518.Contains (rootPhase 518) := by
  have hh := CBox.mul_contains_e root259_contains root259_contains (c:=root518) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid519_contains : mid519.Contains (rootPhase 518) := root518_contains
lemma root519_contains : root519.Contains (rootPhase 519) := by
  have hh := CBox.mul_contains_e mid519_contains root1_contains (c:=root519) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root520_contains : root520.Contains (rootPhase 520) := by
  have hh := CBox.mul_contains_e root260_contains root260_contains (c:=root520) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid521_contains : mid521.Contains (rootPhase 520) := root520_contains
lemma root521_contains : root521.Contains (rootPhase 521) := by
  have hh := CBox.mul_contains_e mid521_contains root1_contains (c:=root521) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root522_contains : root522.Contains (rootPhase 522) := by
  have hh := CBox.mul_contains_e root261_contains root261_contains (c:=root522) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid523_contains : mid523.Contains (rootPhase 522) := root522_contains
lemma root523_contains : root523.Contains (rootPhase 523) := by
  have hh := CBox.mul_contains_e mid523_contains root1_contains (c:=root523) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root524_contains : root524.Contains (rootPhase 524) := by
  have hh := CBox.mul_contains_e root262_contains root262_contains (c:=root524) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid525_contains : mid525.Contains (rootPhase 524) := root524_contains
lemma root525_contains : root525.Contains (rootPhase 525) := by
  have hh := CBox.mul_contains_e mid525_contains root1_contains (c:=root525) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root526_contains : root526.Contains (rootPhase 526) := by
  have hh := CBox.mul_contains_e root263_contains root263_contains (c:=root526) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid527_contains : mid527.Contains (rootPhase 526) := root526_contains
lemma root527_contains : root527.Contains (rootPhase 527) := by
  have hh := CBox.mul_contains_e mid527_contains root1_contains (c:=root527) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root528_contains : root528.Contains (rootPhase 528) := by
  have hh := CBox.mul_contains_e root264_contains root264_contains (c:=root528) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid529_contains : mid529.Contains (rootPhase 528) := root528_contains
lemma root529_contains : root529.Contains (rootPhase 529) := by
  have hh := CBox.mul_contains_e mid529_contains root1_contains (c:=root529) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root530_contains : root530.Contains (rootPhase 530) := by
  have hh := CBox.mul_contains_e root265_contains root265_contains (c:=root530) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid531_contains : mid531.Contains (rootPhase 530) := root530_contains
lemma root531_contains : root531.Contains (rootPhase 531) := by
  have hh := CBox.mul_contains_e mid531_contains root1_contains (c:=root531) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root532_contains : root532.Contains (rootPhase 532) := by
  have hh := CBox.mul_contains_e root266_contains root266_contains (c:=root532) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid533_contains : mid533.Contains (rootPhase 532) := root532_contains
lemma root533_contains : root533.Contains (rootPhase 533) := by
  have hh := CBox.mul_contains_e mid533_contains root1_contains (c:=root533) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root534_contains : root534.Contains (rootPhase 534) := by
  have hh := CBox.mul_contains_e root267_contains root267_contains (c:=root534) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid535_contains : mid535.Contains (rootPhase 534) := root534_contains
lemma root535_contains : root535.Contains (rootPhase 535) := by
  have hh := CBox.mul_contains_e mid535_contains root1_contains (c:=root535) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root536_contains : root536.Contains (rootPhase 536) := by
  have hh := CBox.mul_contains_e root268_contains root268_contains (c:=root536) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid537_contains : mid537.Contains (rootPhase 536) := root536_contains
lemma root537_contains : root537.Contains (rootPhase 537) := by
  have hh := CBox.mul_contains_e mid537_contains root1_contains (c:=root537) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root538_contains : root538.Contains (rootPhase 538) := by
  have hh := CBox.mul_contains_e root269_contains root269_contains (c:=root538) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid539_contains : mid539.Contains (rootPhase 538) := root538_contains
lemma root539_contains : root539.Contains (rootPhase 539) := by
  have hh := CBox.mul_contains_e mid539_contains root1_contains (c:=root539) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root540_contains : root540.Contains (rootPhase 540) := by
  have hh := CBox.mul_contains_e root270_contains root270_contains (c:=root540) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid541_contains : mid541.Contains (rootPhase 540) := root540_contains
lemma root541_contains : root541.Contains (rootPhase 541) := by
  have hh := CBox.mul_contains_e mid541_contains root1_contains (c:=root541) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root542_contains : root542.Contains (rootPhase 542) := by
  have hh := CBox.mul_contains_e root271_contains root271_contains (c:=root542) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid543_contains : mid543.Contains (rootPhase 542) := root542_contains
lemma root543_contains : root543.Contains (rootPhase 543) := by
  have hh := CBox.mul_contains_e mid543_contains root1_contains (c:=root543) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root544_contains : root544.Contains (rootPhase 544) := by
  have hh := CBox.mul_contains_e root272_contains root272_contains (c:=root544) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid545_contains : mid545.Contains (rootPhase 544) := root544_contains
lemma root545_contains : root545.Contains (rootPhase 545) := by
  have hh := CBox.mul_contains_e mid545_contains root1_contains (c:=root545) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root546_contains : root546.Contains (rootPhase 546) := by
  have hh := CBox.mul_contains_e root273_contains root273_contains (c:=root546) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid547_contains : mid547.Contains (rootPhase 546) := root546_contains
lemma root547_contains : root547.Contains (rootPhase 547) := by
  have hh := CBox.mul_contains_e mid547_contains root1_contains (c:=root547) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root548_contains : root548.Contains (rootPhase 548) := by
  have hh := CBox.mul_contains_e root274_contains root274_contains (c:=root548) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid549_contains : mid549.Contains (rootPhase 548) := root548_contains
lemma root549_contains : root549.Contains (rootPhase 549) := by
  have hh := CBox.mul_contains_e mid549_contains root1_contains (c:=root549) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root550_contains : root550.Contains (rootPhase 550) := by
  have hh := CBox.mul_contains_e root275_contains root275_contains (c:=root550) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid551_contains : mid551.Contains (rootPhase 550) := root550_contains
lemma root551_contains : root551.Contains (rootPhase 551) := by
  have hh := CBox.mul_contains_e mid551_contains root1_contains (c:=root551) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root552_contains : root552.Contains (rootPhase 552) := by
  have hh := CBox.mul_contains_e root276_contains root276_contains (c:=root552) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid553_contains : mid553.Contains (rootPhase 552) := root552_contains
lemma root553_contains : root553.Contains (rootPhase 553) := by
  have hh := CBox.mul_contains_e mid553_contains root1_contains (c:=root553) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root554_contains : root554.Contains (rootPhase 554) := by
  have hh := CBox.mul_contains_e root277_contains root277_contains (c:=root554) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid555_contains : mid555.Contains (rootPhase 554) := root554_contains
lemma root555_contains : root555.Contains (rootPhase 555) := by
  have hh := CBox.mul_contains_e mid555_contains root1_contains (c:=root555) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root556_contains : root556.Contains (rootPhase 556) := by
  have hh := CBox.mul_contains_e root278_contains root278_contains (c:=root556) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid557_contains : mid557.Contains (rootPhase 556) := root556_contains
lemma root557_contains : root557.Contains (rootPhase 557) := by
  have hh := CBox.mul_contains_e mid557_contains root1_contains (c:=root557) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root558_contains : root558.Contains (rootPhase 558) := by
  have hh := CBox.mul_contains_e root279_contains root279_contains (c:=root558) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid559_contains : mid559.Contains (rootPhase 558) := root558_contains
lemma root559_contains : root559.Contains (rootPhase 559) := by
  have hh := CBox.mul_contains_e mid559_contains root1_contains (c:=root559) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root560_contains : root560.Contains (rootPhase 560) := by
  have hh := CBox.mul_contains_e root280_contains root280_contains (c:=root560) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid561_contains : mid561.Contains (rootPhase 560) := root560_contains
lemma root561_contains : root561.Contains (rootPhase 561) := by
  have hh := CBox.mul_contains_e mid561_contains root1_contains (c:=root561) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root562_contains : root562.Contains (rootPhase 562) := by
  have hh := CBox.mul_contains_e root281_contains root281_contains (c:=root562) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid563_contains : mid563.Contains (rootPhase 562) := root562_contains
lemma root563_contains : root563.Contains (rootPhase 563) := by
  have hh := CBox.mul_contains_e mid563_contains root1_contains (c:=root563) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root564_contains : root564.Contains (rootPhase 564) := by
  have hh := CBox.mul_contains_e root282_contains root282_contains (c:=root564) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid565_contains : mid565.Contains (rootPhase 564) := root564_contains
lemma root565_contains : root565.Contains (rootPhase 565) := by
  have hh := CBox.mul_contains_e mid565_contains root1_contains (c:=root565) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root566_contains : root566.Contains (rootPhase 566) := by
  have hh := CBox.mul_contains_e root283_contains root283_contains (c:=root566) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid567_contains : mid567.Contains (rootPhase 566) := root566_contains
lemma root567_contains : root567.Contains (rootPhase 567) := by
  have hh := CBox.mul_contains_e mid567_contains root1_contains (c:=root567) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root568_contains : root568.Contains (rootPhase 568) := by
  have hh := CBox.mul_contains_e root284_contains root284_contains (c:=root568) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid569_contains : mid569.Contains (rootPhase 568) := root568_contains
lemma root569_contains : root569.Contains (rootPhase 569) := by
  have hh := CBox.mul_contains_e mid569_contains root1_contains (c:=root569) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root570_contains : root570.Contains (rootPhase 570) := by
  have hh := CBox.mul_contains_e root285_contains root285_contains (c:=root570) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid571_contains : mid571.Contains (rootPhase 570) := root570_contains
lemma root571_contains : root571.Contains (rootPhase 571) := by
  have hh := CBox.mul_contains_e mid571_contains root1_contains (c:=root571) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root572_contains : root572.Contains (rootPhase 572) := by
  have hh := CBox.mul_contains_e root286_contains root286_contains (c:=root572) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid573_contains : mid573.Contains (rootPhase 572) := root572_contains
lemma root573_contains : root573.Contains (rootPhase 573) := by
  have hh := CBox.mul_contains_e mid573_contains root1_contains (c:=root573) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root574_contains : root574.Contains (rootPhase 574) := by
  have hh := CBox.mul_contains_e root287_contains root287_contains (c:=root574) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid575_contains : mid575.Contains (rootPhase 574) := root574_contains
lemma root575_contains : root575.Contains (rootPhase 575) := by
  have hh := CBox.mul_contains_e mid575_contains root1_contains (c:=root575) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root576_contains : root576.Contains (rootPhase 576) := by
  have hh := CBox.mul_contains_e root288_contains root288_contains (c:=root576) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid577_contains : mid577.Contains (rootPhase 576) := root576_contains
lemma root577_contains : root577.Contains (rootPhase 577) := by
  have hh := CBox.mul_contains_e mid577_contains root1_contains (c:=root577) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root578_contains : root578.Contains (rootPhase 578) := by
  have hh := CBox.mul_contains_e root289_contains root289_contains (c:=root578) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid579_contains : mid579.Contains (rootPhase 578) := root578_contains
lemma root579_contains : root579.Contains (rootPhase 579) := by
  have hh := CBox.mul_contains_e mid579_contains root1_contains (c:=root579) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root580_contains : root580.Contains (rootPhase 580) := by
  have hh := CBox.mul_contains_e root290_contains root290_contains (c:=root580) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid581_contains : mid581.Contains (rootPhase 580) := root580_contains
lemma root581_contains : root581.Contains (rootPhase 581) := by
  have hh := CBox.mul_contains_e mid581_contains root1_contains (c:=root581) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root582_contains : root582.Contains (rootPhase 582) := by
  have hh := CBox.mul_contains_e root291_contains root291_contains (c:=root582) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid583_contains : mid583.Contains (rootPhase 582) := root582_contains
lemma root583_contains : root583.Contains (rootPhase 583) := by
  have hh := CBox.mul_contains_e mid583_contains root1_contains (c:=root583) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root584_contains : root584.Contains (rootPhase 584) := by
  have hh := CBox.mul_contains_e root292_contains root292_contains (c:=root584) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid585_contains : mid585.Contains (rootPhase 584) := root584_contains
lemma root585_contains : root585.Contains (rootPhase 585) := by
  have hh := CBox.mul_contains_e mid585_contains root1_contains (c:=root585) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root586_contains : root586.Contains (rootPhase 586) := by
  have hh := CBox.mul_contains_e root293_contains root293_contains (c:=root586) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid587_contains : mid587.Contains (rootPhase 586) := root586_contains
lemma root587_contains : root587.Contains (rootPhase 587) := by
  have hh := CBox.mul_contains_e mid587_contains root1_contains (c:=root587) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root588_contains : root588.Contains (rootPhase 588) := by
  have hh := CBox.mul_contains_e root294_contains root294_contains (c:=root588) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid589_contains : mid589.Contains (rootPhase 588) := root588_contains
lemma root589_contains : root589.Contains (rootPhase 589) := by
  have hh := CBox.mul_contains_e mid589_contains root1_contains (c:=root589) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root590_contains : root590.Contains (rootPhase 590) := by
  have hh := CBox.mul_contains_e root295_contains root295_contains (c:=root590) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid591_contains : mid591.Contains (rootPhase 590) := root590_contains
lemma root591_contains : root591.Contains (rootPhase 591) := by
  have hh := CBox.mul_contains_e mid591_contains root1_contains (c:=root591) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root592_contains : root592.Contains (rootPhase 592) := by
  have hh := CBox.mul_contains_e root296_contains root296_contains (c:=root592) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid593_contains : mid593.Contains (rootPhase 592) := root592_contains
lemma root593_contains : root593.Contains (rootPhase 593) := by
  have hh := CBox.mul_contains_e mid593_contains root1_contains (c:=root593) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root594_contains : root594.Contains (rootPhase 594) := by
  have hh := CBox.mul_contains_e root297_contains root297_contains (c:=root594) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid595_contains : mid595.Contains (rootPhase 594) := root594_contains
lemma root595_contains : root595.Contains (rootPhase 595) := by
  have hh := CBox.mul_contains_e mid595_contains root1_contains (c:=root595) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root596_contains : root596.Contains (rootPhase 596) := by
  have hh := CBox.mul_contains_e root298_contains root298_contains (c:=root596) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid597_contains : mid597.Contains (rootPhase 596) := root596_contains
lemma root597_contains : root597.Contains (rootPhase 597) := by
  have hh := CBox.mul_contains_e mid597_contains root1_contains (c:=root597) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root598_contains : root598.Contains (rootPhase 598) := by
  have hh := CBox.mul_contains_e root299_contains root299_contains (c:=root598) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid599_contains : mid599.Contains (rootPhase 598) := root598_contains
lemma root599_contains : root599.Contains (rootPhase 599) := by
  have hh := CBox.mul_contains_e mid599_contains root1_contains (c:=root599) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root600_contains : root600.Contains (rootPhase 600) := by
  have hh := CBox.mul_contains_e root300_contains root300_contains (c:=root600) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid601_contains : mid601.Contains (rootPhase 600) := root600_contains
lemma root601_contains : root601.Contains (rootPhase 601) := by
  have hh := CBox.mul_contains_e mid601_contains root1_contains (c:=root601) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root602_contains : root602.Contains (rootPhase 602) := by
  have hh := CBox.mul_contains_e root301_contains root301_contains (c:=root602) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid603_contains : mid603.Contains (rootPhase 602) := root602_contains
lemma root603_contains : root603.Contains (rootPhase 603) := by
  have hh := CBox.mul_contains_e mid603_contains root1_contains (c:=root603) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root604_contains : root604.Contains (rootPhase 604) := by
  have hh := CBox.mul_contains_e root302_contains root302_contains (c:=root604) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid605_contains : mid605.Contains (rootPhase 604) := root604_contains
lemma root605_contains : root605.Contains (rootPhase 605) := by
  have hh := CBox.mul_contains_e mid605_contains root1_contains (c:=root605) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root606_contains : root606.Contains (rootPhase 606) := by
  have hh := CBox.mul_contains_e root303_contains root303_contains (c:=root606) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid607_contains : mid607.Contains (rootPhase 606) := root606_contains
lemma root607_contains : root607.Contains (rootPhase 607) := by
  have hh := CBox.mul_contains_e mid607_contains root1_contains (c:=root607) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root608_contains : root608.Contains (rootPhase 608) := by
  have hh := CBox.mul_contains_e root304_contains root304_contains (c:=root608) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid609_contains : mid609.Contains (rootPhase 608) := root608_contains
lemma root609_contains : root609.Contains (rootPhase 609) := by
  have hh := CBox.mul_contains_e mid609_contains root1_contains (c:=root609) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root610_contains : root610.Contains (rootPhase 610) := by
  have hh := CBox.mul_contains_e root305_contains root305_contains (c:=root610) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid611_contains : mid611.Contains (rootPhase 610) := root610_contains
lemma root611_contains : root611.Contains (rootPhase 611) := by
  have hh := CBox.mul_contains_e mid611_contains root1_contains (c:=root611) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root612_contains : root612.Contains (rootPhase 612) := by
  have hh := CBox.mul_contains_e root306_contains root306_contains (c:=root612) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid613_contains : mid613.Contains (rootPhase 612) := root612_contains
lemma root613_contains : root613.Contains (rootPhase 613) := by
  have hh := CBox.mul_contains_e mid613_contains root1_contains (c:=root613) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root614_contains : root614.Contains (rootPhase 614) := by
  have hh := CBox.mul_contains_e root307_contains root307_contains (c:=root614) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid615_contains : mid615.Contains (rootPhase 614) := root614_contains
lemma root615_contains : root615.Contains (rootPhase 615) := by
  have hh := CBox.mul_contains_e mid615_contains root1_contains (c:=root615) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root616_contains : root616.Contains (rootPhase 616) := by
  have hh := CBox.mul_contains_e root308_contains root308_contains (c:=root616) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid617_contains : mid617.Contains (rootPhase 616) := root616_contains
lemma root617_contains : root617.Contains (rootPhase 617) := by
  have hh := CBox.mul_contains_e mid617_contains root1_contains (c:=root617) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root618_contains : root618.Contains (rootPhase 618) := by
  have hh := CBox.mul_contains_e root309_contains root309_contains (c:=root618) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid619_contains : mid619.Contains (rootPhase 618) := root618_contains
lemma root619_contains : root619.Contains (rootPhase 619) := by
  have hh := CBox.mul_contains_e mid619_contains root1_contains (c:=root619) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root620_contains : root620.Contains (rootPhase 620) := by
  have hh := CBox.mul_contains_e root310_contains root310_contains (c:=root620) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid621_contains : mid621.Contains (rootPhase 620) := root620_contains
lemma root621_contains : root621.Contains (rootPhase 621) := by
  have hh := CBox.mul_contains_e mid621_contains root1_contains (c:=root621) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root622_contains : root622.Contains (rootPhase 622) := by
  have hh := CBox.mul_contains_e root311_contains root311_contains (c:=root622) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid623_contains : mid623.Contains (rootPhase 622) := root622_contains
lemma root623_contains : root623.Contains (rootPhase 623) := by
  have hh := CBox.mul_contains_e mid623_contains root1_contains (c:=root623) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root624_contains : root624.Contains (rootPhase 624) := by
  have hh := CBox.mul_contains_e root312_contains root312_contains (c:=root624) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid625_contains : mid625.Contains (rootPhase 624) := root624_contains
lemma root625_contains : root625.Contains (rootPhase 625) := by
  have hh := CBox.mul_contains_e mid625_contains root1_contains (c:=root625) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root626_contains : root626.Contains (rootPhase 626) := by
  have hh := CBox.mul_contains_e root313_contains root313_contains (c:=root626) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid627_contains : mid627.Contains (rootPhase 626) := root626_contains
lemma root627_contains : root627.Contains (rootPhase 627) := by
  have hh := CBox.mul_contains_e mid627_contains root1_contains (c:=root627) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root628_contains : root628.Contains (rootPhase 628) := by
  have hh := CBox.mul_contains_e root314_contains root314_contains (c:=root628) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid629_contains : mid629.Contains (rootPhase 628) := root628_contains
lemma root629_contains : root629.Contains (rootPhase 629) := by
  have hh := CBox.mul_contains_e mid629_contains root1_contains (c:=root629) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root630_contains : root630.Contains (rootPhase 630) := by
  have hh := CBox.mul_contains_e root315_contains root315_contains (c:=root630) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid631_contains : mid631.Contains (rootPhase 630) := root630_contains
lemma root631_contains : root631.Contains (rootPhase 631) := by
  have hh := CBox.mul_contains_e mid631_contains root1_contains (c:=root631) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root632_contains : root632.Contains (rootPhase 632) := by
  have hh := CBox.mul_contains_e root316_contains root316_contains (c:=root632) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid633_contains : mid633.Contains (rootPhase 632) := root632_contains
lemma root633_contains : root633.Contains (rootPhase 633) := by
  have hh := CBox.mul_contains_e mid633_contains root1_contains (c:=root633) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root634_contains : root634.Contains (rootPhase 634) := by
  have hh := CBox.mul_contains_e root317_contains root317_contains (c:=root634) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid635_contains : mid635.Contains (rootPhase 634) := root634_contains
lemma root635_contains : root635.Contains (rootPhase 635) := by
  have hh := CBox.mul_contains_e mid635_contains root1_contains (c:=root635) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root636_contains : root636.Contains (rootPhase 636) := by
  have hh := CBox.mul_contains_e root318_contains root318_contains (c:=root636) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid637_contains : mid637.Contains (rootPhase 636) := root636_contains
lemma root637_contains : root637.Contains (rootPhase 637) := by
  have hh := CBox.mul_contains_e mid637_contains root1_contains (c:=root637) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root638_contains : root638.Contains (rootPhase 638) := by
  have hh := CBox.mul_contains_e root319_contains root319_contains (c:=root638) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid639_contains : mid639.Contains (rootPhase 638) := root638_contains
lemma root639_contains : root639.Contains (rootPhase 639) := by
  have hh := CBox.mul_contains_e mid639_contains root1_contains (c:=root639) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root640_contains : root640.Contains (rootPhase 640) := by
  have hh := CBox.mul_contains_e root320_contains root320_contains (c:=root640) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid641_contains : mid641.Contains (rootPhase 640) := root640_contains
lemma root641_contains : root641.Contains (rootPhase 641) := by
  have hh := CBox.mul_contains_e mid641_contains root1_contains (c:=root641) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root642_contains : root642.Contains (rootPhase 642) := by
  have hh := CBox.mul_contains_e root321_contains root321_contains (c:=root642) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid643_contains : mid643.Contains (rootPhase 642) := root642_contains
lemma root643_contains : root643.Contains (rootPhase 643) := by
  have hh := CBox.mul_contains_e mid643_contains root1_contains (c:=root643) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root644_contains : root644.Contains (rootPhase 644) := by
  have hh := CBox.mul_contains_e root322_contains root322_contains (c:=root644) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid645_contains : mid645.Contains (rootPhase 644) := root644_contains
lemma root645_contains : root645.Contains (rootPhase 645) := by
  have hh := CBox.mul_contains_e mid645_contains root1_contains (c:=root645) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root646_contains : root646.Contains (rootPhase 646) := by
  have hh := CBox.mul_contains_e root323_contains root323_contains (c:=root646) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid647_contains : mid647.Contains (rootPhase 646) := root646_contains
lemma root647_contains : root647.Contains (rootPhase 647) := by
  have hh := CBox.mul_contains_e mid647_contains root1_contains (c:=root647) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root648_contains : root648.Contains (rootPhase 648) := by
  have hh := CBox.mul_contains_e root324_contains root324_contains (c:=root648) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid649_contains : mid649.Contains (rootPhase 648) := root648_contains
lemma root649_contains : root649.Contains (rootPhase 649) := by
  have hh := CBox.mul_contains_e mid649_contains root1_contains (c:=root649) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root650_contains : root650.Contains (rootPhase 650) := by
  have hh := CBox.mul_contains_e root325_contains root325_contains (c:=root650) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid651_contains : mid651.Contains (rootPhase 650) := root650_contains
lemma root651_contains : root651.Contains (rootPhase 651) := by
  have hh := CBox.mul_contains_e mid651_contains root1_contains (c:=root651) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root652_contains : root652.Contains (rootPhase 652) := by
  have hh := CBox.mul_contains_e root326_contains root326_contains (c:=root652) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid653_contains : mid653.Contains (rootPhase 652) := root652_contains
lemma root653_contains : root653.Contains (rootPhase 653) := by
  have hh := CBox.mul_contains_e mid653_contains root1_contains (c:=root653) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root654_contains : root654.Contains (rootPhase 654) := by
  have hh := CBox.mul_contains_e root327_contains root327_contains (c:=root654) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid655_contains : mid655.Contains (rootPhase 654) := root654_contains
lemma root655_contains : root655.Contains (rootPhase 655) := by
  have hh := CBox.mul_contains_e mid655_contains root1_contains (c:=root655) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root656_contains : root656.Contains (rootPhase 656) := by
  have hh := CBox.mul_contains_e root328_contains root328_contains (c:=root656) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid657_contains : mid657.Contains (rootPhase 656) := root656_contains
lemma root657_contains : root657.Contains (rootPhase 657) := by
  have hh := CBox.mul_contains_e mid657_contains root1_contains (c:=root657) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root658_contains : root658.Contains (rootPhase 658) := by
  have hh := CBox.mul_contains_e root329_contains root329_contains (c:=root658) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid659_contains : mid659.Contains (rootPhase 658) := root658_contains
lemma root659_contains : root659.Contains (rootPhase 659) := by
  have hh := CBox.mul_contains_e mid659_contains root1_contains (c:=root659) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root660_contains : root660.Contains (rootPhase 660) := by
  have hh := CBox.mul_contains_e root330_contains root330_contains (c:=root660) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid661_contains : mid661.Contains (rootPhase 660) := root660_contains
lemma root661_contains : root661.Contains (rootPhase 661) := by
  have hh := CBox.mul_contains_e mid661_contains root1_contains (c:=root661) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root662_contains : root662.Contains (rootPhase 662) := by
  have hh := CBox.mul_contains_e root331_contains root331_contains (c:=root662) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid663_contains : mid663.Contains (rootPhase 662) := root662_contains
lemma root663_contains : root663.Contains (rootPhase 663) := by
  have hh := CBox.mul_contains_e mid663_contains root1_contains (c:=root663) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root664_contains : root664.Contains (rootPhase 664) := by
  have hh := CBox.mul_contains_e root332_contains root332_contains (c:=root664) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid665_contains : mid665.Contains (rootPhase 664) := root664_contains
lemma root665_contains : root665.Contains (rootPhase 665) := by
  have hh := CBox.mul_contains_e mid665_contains root1_contains (c:=root665) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root666_contains : root666.Contains (rootPhase 666) := by
  have hh := CBox.mul_contains_e root333_contains root333_contains (c:=root666) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid667_contains : mid667.Contains (rootPhase 666) := root666_contains
lemma root667_contains : root667.Contains (rootPhase 667) := by
  have hh := CBox.mul_contains_e mid667_contains root1_contains (c:=root667) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root668_contains : root668.Contains (rootPhase 668) := by
  have hh := CBox.mul_contains_e root334_contains root334_contains (c:=root668) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid669_contains : mid669.Contains (rootPhase 668) := root668_contains
lemma root669_contains : root669.Contains (rootPhase 669) := by
  have hh := CBox.mul_contains_e mid669_contains root1_contains (c:=root669) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root670_contains : root670.Contains (rootPhase 670) := by
  have hh := CBox.mul_contains_e root335_contains root335_contains (c:=root670) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid671_contains : mid671.Contains (rootPhase 670) := root670_contains
lemma root671_contains : root671.Contains (rootPhase 671) := by
  have hh := CBox.mul_contains_e mid671_contains root1_contains (c:=root671) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root672_contains : root672.Contains (rootPhase 672) := by
  have hh := CBox.mul_contains_e root336_contains root336_contains (c:=root672) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid673_contains : mid673.Contains (rootPhase 672) := root672_contains
lemma root673_contains : root673.Contains (rootPhase 673) := by
  have hh := CBox.mul_contains_e mid673_contains root1_contains (c:=root673) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root674_contains : root674.Contains (rootPhase 674) := by
  have hh := CBox.mul_contains_e root337_contains root337_contains (c:=root674) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid675_contains : mid675.Contains (rootPhase 674) := root674_contains
lemma root675_contains : root675.Contains (rootPhase 675) := by
  have hh := CBox.mul_contains_e mid675_contains root1_contains (c:=root675) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root676_contains : root676.Contains (rootPhase 676) := by
  have hh := CBox.mul_contains_e root338_contains root338_contains (c:=root676) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid677_contains : mid677.Contains (rootPhase 676) := root676_contains
lemma root677_contains : root677.Contains (rootPhase 677) := by
  have hh := CBox.mul_contains_e mid677_contains root1_contains (c:=root677) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root678_contains : root678.Contains (rootPhase 678) := by
  have hh := CBox.mul_contains_e root339_contains root339_contains (c:=root678) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid679_contains : mid679.Contains (rootPhase 678) := root678_contains
lemma root679_contains : root679.Contains (rootPhase 679) := by
  have hh := CBox.mul_contains_e mid679_contains root1_contains (c:=root679) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root680_contains : root680.Contains (rootPhase 680) := by
  have hh := CBox.mul_contains_e root340_contains root340_contains (c:=root680) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid681_contains : mid681.Contains (rootPhase 680) := root680_contains
lemma root681_contains : root681.Contains (rootPhase 681) := by
  have hh := CBox.mul_contains_e mid681_contains root1_contains (c:=root681) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root682_contains : root682.Contains (rootPhase 682) := by
  have hh := CBox.mul_contains_e root341_contains root341_contains (c:=root682) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid683_contains : mid683.Contains (rootPhase 682) := root682_contains
lemma root683_contains : root683.Contains (rootPhase 683) := by
  have hh := CBox.mul_contains_e mid683_contains root1_contains (c:=root683) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root684_contains : root684.Contains (rootPhase 684) := by
  have hh := CBox.mul_contains_e root342_contains root342_contains (c:=root684) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid685_contains : mid685.Contains (rootPhase 684) := root684_contains
lemma root685_contains : root685.Contains (rootPhase 685) := by
  have hh := CBox.mul_contains_e mid685_contains root1_contains (c:=root685) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root686_contains : root686.Contains (rootPhase 686) := by
  have hh := CBox.mul_contains_e root343_contains root343_contains (c:=root686) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid687_contains : mid687.Contains (rootPhase 686) := root686_contains
lemma root687_contains : root687.Contains (rootPhase 687) := by
  have hh := CBox.mul_contains_e mid687_contains root1_contains (c:=root687) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root688_contains : root688.Contains (rootPhase 688) := by
  have hh := CBox.mul_contains_e root344_contains root344_contains (c:=root688) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid689_contains : mid689.Contains (rootPhase 688) := root688_contains
lemma root689_contains : root689.Contains (rootPhase 689) := by
  have hh := CBox.mul_contains_e mid689_contains root1_contains (c:=root689) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root690_contains : root690.Contains (rootPhase 690) := by
  have hh := CBox.mul_contains_e root345_contains root345_contains (c:=root690) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid691_contains : mid691.Contains (rootPhase 690) := root690_contains
lemma root691_contains : root691.Contains (rootPhase 691) := by
  have hh := CBox.mul_contains_e mid691_contains root1_contains (c:=root691) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root692_contains : root692.Contains (rootPhase 692) := by
  have hh := CBox.mul_contains_e root346_contains root346_contains (c:=root692) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid693_contains : mid693.Contains (rootPhase 692) := root692_contains
lemma root693_contains : root693.Contains (rootPhase 693) := by
  have hh := CBox.mul_contains_e mid693_contains root1_contains (c:=root693) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root694_contains : root694.Contains (rootPhase 694) := by
  have hh := CBox.mul_contains_e root347_contains root347_contains (c:=root694) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid695_contains : mid695.Contains (rootPhase 694) := root694_contains
lemma root695_contains : root695.Contains (rootPhase 695) := by
  have hh := CBox.mul_contains_e mid695_contains root1_contains (c:=root695) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root696_contains : root696.Contains (rootPhase 696) := by
  have hh := CBox.mul_contains_e root348_contains root348_contains (c:=root696) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid697_contains : mid697.Contains (rootPhase 696) := root696_contains
lemma root697_contains : root697.Contains (rootPhase 697) := by
  have hh := CBox.mul_contains_e mid697_contains root1_contains (c:=root697) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root698_contains : root698.Contains (rootPhase 698) := by
  have hh := CBox.mul_contains_e root349_contains root349_contains (c:=root698) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid699_contains : mid699.Contains (rootPhase 698) := root698_contains
lemma root699_contains : root699.Contains (rootPhase 699) := by
  have hh := CBox.mul_contains_e mid699_contains root1_contains (c:=root699) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root700_contains : root700.Contains (rootPhase 700) := by
  have hh := CBox.mul_contains_e root350_contains root350_contains (c:=root700) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid701_contains : mid701.Contains (rootPhase 700) := root700_contains
lemma root701_contains : root701.Contains (rootPhase 701) := by
  have hh := CBox.mul_contains_e mid701_contains root1_contains (c:=root701) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root702_contains : root702.Contains (rootPhase 702) := by
  have hh := CBox.mul_contains_e root351_contains root351_contains (c:=root702) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid703_contains : mid703.Contains (rootPhase 702) := root702_contains
lemma root703_contains : root703.Contains (rootPhase 703) := by
  have hh := CBox.mul_contains_e mid703_contains root1_contains (c:=root703) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root704_contains : root704.Contains (rootPhase 704) := by
  have hh := CBox.mul_contains_e root352_contains root352_contains (c:=root704) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid705_contains : mid705.Contains (rootPhase 704) := root704_contains
lemma root705_contains : root705.Contains (rootPhase 705) := by
  have hh := CBox.mul_contains_e mid705_contains root1_contains (c:=root705) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root706_contains : root706.Contains (rootPhase 706) := by
  have hh := CBox.mul_contains_e root353_contains root353_contains (c:=root706) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid707_contains : mid707.Contains (rootPhase 706) := root706_contains
lemma root707_contains : root707.Contains (rootPhase 707) := by
  have hh := CBox.mul_contains_e mid707_contains root1_contains (c:=root707) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root708_contains : root708.Contains (rootPhase 708) := by
  have hh := CBox.mul_contains_e root354_contains root354_contains (c:=root708) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid709_contains : mid709.Contains (rootPhase 708) := root708_contains
lemma root709_contains : root709.Contains (rootPhase 709) := by
  have hh := CBox.mul_contains_e mid709_contains root1_contains (c:=root709) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root710_contains : root710.Contains (rootPhase 710) := by
  have hh := CBox.mul_contains_e root355_contains root355_contains (c:=root710) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid711_contains : mid711.Contains (rootPhase 710) := root710_contains
lemma root711_contains : root711.Contains (rootPhase 711) := by
  have hh := CBox.mul_contains_e mid711_contains root1_contains (c:=root711) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root712_contains : root712.Contains (rootPhase 712) := by
  have hh := CBox.mul_contains_e root356_contains root356_contains (c:=root712) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid713_contains : mid713.Contains (rootPhase 712) := root712_contains
lemma root713_contains : root713.Contains (rootPhase 713) := by
  have hh := CBox.mul_contains_e mid713_contains root1_contains (c:=root713) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root714_contains : root714.Contains (rootPhase 714) := by
  have hh := CBox.mul_contains_e root357_contains root357_contains (c:=root714) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid715_contains : mid715.Contains (rootPhase 714) := root714_contains
lemma root715_contains : root715.Contains (rootPhase 715) := by
  have hh := CBox.mul_contains_e mid715_contains root1_contains (c:=root715) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root716_contains : root716.Contains (rootPhase 716) := by
  have hh := CBox.mul_contains_e root358_contains root358_contains (c:=root716) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid717_contains : mid717.Contains (rootPhase 716) := root716_contains
lemma root717_contains : root717.Contains (rootPhase 717) := by
  have hh := CBox.mul_contains_e mid717_contains root1_contains (c:=root717) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root718_contains : root718.Contains (rootPhase 718) := by
  have hh := CBox.mul_contains_e root359_contains root359_contains (c:=root718) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid719_contains : mid719.Contains (rootPhase 718) := root718_contains
lemma root719_contains : root719.Contains (rootPhase 719) := by
  have hh := CBox.mul_contains_e mid719_contains root1_contains (c:=root719) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root720_contains : root720.Contains (rootPhase 720) := by
  have hh := CBox.mul_contains_e root360_contains root360_contains (c:=root720) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid721_contains : mid721.Contains (rootPhase 720) := root720_contains
lemma root721_contains : root721.Contains (rootPhase 721) := by
  have hh := CBox.mul_contains_e mid721_contains root1_contains (c:=root721) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root722_contains : root722.Contains (rootPhase 722) := by
  have hh := CBox.mul_contains_e root361_contains root361_contains (c:=root722) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid723_contains : mid723.Contains (rootPhase 722) := root722_contains
lemma root723_contains : root723.Contains (rootPhase 723) := by
  have hh := CBox.mul_contains_e mid723_contains root1_contains (c:=root723) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root724_contains : root724.Contains (rootPhase 724) := by
  have hh := CBox.mul_contains_e root362_contains root362_contains (c:=root724) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid725_contains : mid725.Contains (rootPhase 724) := root724_contains
lemma root725_contains : root725.Contains (rootPhase 725) := by
  have hh := CBox.mul_contains_e mid725_contains root1_contains (c:=root725) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root726_contains : root726.Contains (rootPhase 726) := by
  have hh := CBox.mul_contains_e root363_contains root363_contains (c:=root726) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid727_contains : mid727.Contains (rootPhase 726) := root726_contains
lemma root727_contains : root727.Contains (rootPhase 727) := by
  have hh := CBox.mul_contains_e mid727_contains root1_contains (c:=root727) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root728_contains : root728.Contains (rootPhase 728) := by
  have hh := CBox.mul_contains_e root364_contains root364_contains (c:=root728) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid729_contains : mid729.Contains (rootPhase 728) := root728_contains
lemma root729_contains : root729.Contains (rootPhase 729) := by
  have hh := CBox.mul_contains_e mid729_contains root1_contains (c:=root729) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root730_contains : root730.Contains (rootPhase 730) := by
  have hh := CBox.mul_contains_e root365_contains root365_contains (c:=root730) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid731_contains : mid731.Contains (rootPhase 730) := root730_contains
lemma root731_contains : root731.Contains (rootPhase 731) := by
  have hh := CBox.mul_contains_e mid731_contains root1_contains (c:=root731) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root732_contains : root732.Contains (rootPhase 732) := by
  have hh := CBox.mul_contains_e root366_contains root366_contains (c:=root732) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid733_contains : mid733.Contains (rootPhase 732) := root732_contains
lemma root733_contains : root733.Contains (rootPhase 733) := by
  have hh := CBox.mul_contains_e mid733_contains root1_contains (c:=root733) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root734_contains : root734.Contains (rootPhase 734) := by
  have hh := CBox.mul_contains_e root367_contains root367_contains (c:=root734) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid735_contains : mid735.Contains (rootPhase 734) := root734_contains
lemma root735_contains : root735.Contains (rootPhase 735) := by
  have hh := CBox.mul_contains_e mid735_contains root1_contains (c:=root735) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root736_contains : root736.Contains (rootPhase 736) := by
  have hh := CBox.mul_contains_e root368_contains root368_contains (c:=root736) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid737_contains : mid737.Contains (rootPhase 736) := root736_contains
lemma root737_contains : root737.Contains (rootPhase 737) := by
  have hh := CBox.mul_contains_e mid737_contains root1_contains (c:=root737) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root738_contains : root738.Contains (rootPhase 738) := by
  have hh := CBox.mul_contains_e root369_contains root369_contains (c:=root738) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid739_contains : mid739.Contains (rootPhase 738) := root738_contains
lemma root739_contains : root739.Contains (rootPhase 739) := by
  have hh := CBox.mul_contains_e mid739_contains root1_contains (c:=root739) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root740_contains : root740.Contains (rootPhase 740) := by
  have hh := CBox.mul_contains_e root370_contains root370_contains (c:=root740) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid741_contains : mid741.Contains (rootPhase 740) := root740_contains
lemma root741_contains : root741.Contains (rootPhase 741) := by
  have hh := CBox.mul_contains_e mid741_contains root1_contains (c:=root741) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root742_contains : root742.Contains (rootPhase 742) := by
  have hh := CBox.mul_contains_e root371_contains root371_contains (c:=root742) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid743_contains : mid743.Contains (rootPhase 742) := root742_contains
lemma root743_contains : root743.Contains (rootPhase 743) := by
  have hh := CBox.mul_contains_e mid743_contains root1_contains (c:=root743) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root744_contains : root744.Contains (rootPhase 744) := by
  have hh := CBox.mul_contains_e root372_contains root372_contains (c:=root744) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid745_contains : mid745.Contains (rootPhase 744) := root744_contains
lemma root745_contains : root745.Contains (rootPhase 745) := by
  have hh := CBox.mul_contains_e mid745_contains root1_contains (c:=root745) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root746_contains : root746.Contains (rootPhase 746) := by
  have hh := CBox.mul_contains_e root373_contains root373_contains (c:=root746) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid747_contains : mid747.Contains (rootPhase 746) := root746_contains
lemma root747_contains : root747.Contains (rootPhase 747) := by
  have hh := CBox.mul_contains_e mid747_contains root1_contains (c:=root747) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root748_contains : root748.Contains (rootPhase 748) := by
  have hh := CBox.mul_contains_e root374_contains root374_contains (c:=root748) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid749_contains : mid749.Contains (rootPhase 748) := root748_contains
lemma root749_contains : root749.Contains (rootPhase 749) := by
  have hh := CBox.mul_contains_e mid749_contains root1_contains (c:=root749) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root750_contains : root750.Contains (rootPhase 750) := by
  have hh := CBox.mul_contains_e root375_contains root375_contains (c:=root750) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid751_contains : mid751.Contains (rootPhase 750) := root750_contains
lemma root751_contains : root751.Contains (rootPhase 751) := by
  have hh := CBox.mul_contains_e mid751_contains root1_contains (c:=root751) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root752_contains : root752.Contains (rootPhase 752) := by
  have hh := CBox.mul_contains_e root376_contains root376_contains (c:=root752) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid753_contains : mid753.Contains (rootPhase 752) := root752_contains
lemma root753_contains : root753.Contains (rootPhase 753) := by
  have hh := CBox.mul_contains_e mid753_contains root1_contains (c:=root753) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root754_contains : root754.Contains (rootPhase 754) := by
  have hh := CBox.mul_contains_e root377_contains root377_contains (c:=root754) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid755_contains : mid755.Contains (rootPhase 754) := root754_contains
lemma root755_contains : root755.Contains (rootPhase 755) := by
  have hh := CBox.mul_contains_e mid755_contains root1_contains (c:=root755) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root756_contains : root756.Contains (rootPhase 756) := by
  have hh := CBox.mul_contains_e root378_contains root378_contains (c:=root756) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid757_contains : mid757.Contains (rootPhase 756) := root756_contains
lemma root757_contains : root757.Contains (rootPhase 757) := by
  have hh := CBox.mul_contains_e mid757_contains root1_contains (c:=root757) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root758_contains : root758.Contains (rootPhase 758) := by
  have hh := CBox.mul_contains_e root379_contains root379_contains (c:=root758) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid759_contains : mid759.Contains (rootPhase 758) := root758_contains
lemma root759_contains : root759.Contains (rootPhase 759) := by
  have hh := CBox.mul_contains_e mid759_contains root1_contains (c:=root759) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root760_contains : root760.Contains (rootPhase 760) := by
  have hh := CBox.mul_contains_e root380_contains root380_contains (c:=root760) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid761_contains : mid761.Contains (rootPhase 760) := root760_contains
lemma root761_contains : root761.Contains (rootPhase 761) := by
  have hh := CBox.mul_contains_e mid761_contains root1_contains (c:=root761) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root762_contains : root762.Contains (rootPhase 762) := by
  have hh := CBox.mul_contains_e root381_contains root381_contains (c:=root762) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid763_contains : mid763.Contains (rootPhase 762) := root762_contains
lemma root763_contains : root763.Contains (rootPhase 763) := by
  have hh := CBox.mul_contains_e mid763_contains root1_contains (c:=root763) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root764_contains : root764.Contains (rootPhase 764) := by
  have hh := CBox.mul_contains_e root382_contains root382_contains (c:=root764) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid765_contains : mid765.Contains (rootPhase 764) := root764_contains
lemma root765_contains : root765.Contains (rootPhase 765) := by
  have hh := CBox.mul_contains_e mid765_contains root1_contains (c:=root765) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root766_contains : root766.Contains (rootPhase 766) := by
  have hh := CBox.mul_contains_e root383_contains root383_contains (c:=root766) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid767_contains : mid767.Contains (rootPhase 766) := root766_contains
lemma root767_contains : root767.Contains (rootPhase 767) := by
  have hh := CBox.mul_contains_e mid767_contains root1_contains (c:=root767) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root768_contains : root768.Contains (rootPhase 768) := by
  have hh := CBox.mul_contains_e root384_contains root384_contains (c:=root768) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid769_contains : mid769.Contains (rootPhase 768) := root768_contains
lemma root769_contains : root769.Contains (rootPhase 769) := by
  have hh := CBox.mul_contains_e mid769_contains root1_contains (c:=root769) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root770_contains : root770.Contains (rootPhase 770) := by
  have hh := CBox.mul_contains_e root385_contains root385_contains (c:=root770) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid771_contains : mid771.Contains (rootPhase 770) := root770_contains
lemma root771_contains : root771.Contains (rootPhase 771) := by
  have hh := CBox.mul_contains_e mid771_contains root1_contains (c:=root771) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root772_contains : root772.Contains (rootPhase 772) := by
  have hh := CBox.mul_contains_e root386_contains root386_contains (c:=root772) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid773_contains : mid773.Contains (rootPhase 772) := root772_contains
lemma root773_contains : root773.Contains (rootPhase 773) := by
  have hh := CBox.mul_contains_e mid773_contains root1_contains (c:=root773) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root774_contains : root774.Contains (rootPhase 774) := by
  have hh := CBox.mul_contains_e root387_contains root387_contains (c:=root774) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid775_contains : mid775.Contains (rootPhase 774) := root774_contains
lemma root775_contains : root775.Contains (rootPhase 775) := by
  have hh := CBox.mul_contains_e mid775_contains root1_contains (c:=root775) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root776_contains : root776.Contains (rootPhase 776) := by
  have hh := CBox.mul_contains_e root388_contains root388_contains (c:=root776) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid777_contains : mid777.Contains (rootPhase 776) := root776_contains
lemma root777_contains : root777.Contains (rootPhase 777) := by
  have hh := CBox.mul_contains_e mid777_contains root1_contains (c:=root777) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root778_contains : root778.Contains (rootPhase 778) := by
  have hh := CBox.mul_contains_e root389_contains root389_contains (c:=root778) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid779_contains : mid779.Contains (rootPhase 778) := root778_contains
lemma root779_contains : root779.Contains (rootPhase 779) := by
  have hh := CBox.mul_contains_e mid779_contains root1_contains (c:=root779) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root780_contains : root780.Contains (rootPhase 780) := by
  have hh := CBox.mul_contains_e root390_contains root390_contains (c:=root780) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid781_contains : mid781.Contains (rootPhase 780) := root780_contains
lemma root781_contains : root781.Contains (rootPhase 781) := by
  have hh := CBox.mul_contains_e mid781_contains root1_contains (c:=root781) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root782_contains : root782.Contains (rootPhase 782) := by
  have hh := CBox.mul_contains_e root391_contains root391_contains (c:=root782) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid783_contains : mid783.Contains (rootPhase 782) := root782_contains
lemma root783_contains : root783.Contains (rootPhase 783) := by
  have hh := CBox.mul_contains_e mid783_contains root1_contains (c:=root783) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root784_contains : root784.Contains (rootPhase 784) := by
  have hh := CBox.mul_contains_e root392_contains root392_contains (c:=root784) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid785_contains : mid785.Contains (rootPhase 784) := root784_contains
lemma root785_contains : root785.Contains (rootPhase 785) := by
  have hh := CBox.mul_contains_e mid785_contains root1_contains (c:=root785) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root786_contains : root786.Contains (rootPhase 786) := by
  have hh := CBox.mul_contains_e root393_contains root393_contains (c:=root786) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid787_contains : mid787.Contains (rootPhase 786) := root786_contains
lemma root787_contains : root787.Contains (rootPhase 787) := by
  have hh := CBox.mul_contains_e mid787_contains root1_contains (c:=root787) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root788_contains : root788.Contains (rootPhase 788) := by
  have hh := CBox.mul_contains_e root394_contains root394_contains (c:=root788) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid789_contains : mid789.Contains (rootPhase 788) := root788_contains
lemma root789_contains : root789.Contains (rootPhase 789) := by
  have hh := CBox.mul_contains_e mid789_contains root1_contains (c:=root789) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root790_contains : root790.Contains (rootPhase 790) := by
  have hh := CBox.mul_contains_e root395_contains root395_contains (c:=root790) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid791_contains : mid791.Contains (rootPhase 790) := root790_contains
lemma root791_contains : root791.Contains (rootPhase 791) := by
  have hh := CBox.mul_contains_e mid791_contains root1_contains (c:=root791) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root792_contains : root792.Contains (rootPhase 792) := by
  have hh := CBox.mul_contains_e root396_contains root396_contains (c:=root792) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid793_contains : mid793.Contains (rootPhase 792) := root792_contains
lemma root793_contains : root793.Contains (rootPhase 793) := by
  have hh := CBox.mul_contains_e mid793_contains root1_contains (c:=root793) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root794_contains : root794.Contains (rootPhase 794) := by
  have hh := CBox.mul_contains_e root397_contains root397_contains (c:=root794) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid795_contains : mid795.Contains (rootPhase 794) := root794_contains
lemma root795_contains : root795.Contains (rootPhase 795) := by
  have hh := CBox.mul_contains_e mid795_contains root1_contains (c:=root795) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root796_contains : root796.Contains (rootPhase 796) := by
  have hh := CBox.mul_contains_e root398_contains root398_contains (c:=root796) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid797_contains : mid797.Contains (rootPhase 796) := root796_contains
lemma root797_contains : root797.Contains (rootPhase 797) := by
  have hh := CBox.mul_contains_e mid797_contains root1_contains (c:=root797) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root798_contains : root798.Contains (rootPhase 798) := by
  have hh := CBox.mul_contains_e root399_contains root399_contains (c:=root798) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid799_contains : mid799.Contains (rootPhase 798) := root798_contains
lemma root799_contains : root799.Contains (rootPhase 799) := by
  have hh := CBox.mul_contains_e mid799_contains root1_contains (c:=root799) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root800_contains : root800.Contains (rootPhase 800) := by
  have hh := CBox.mul_contains_e root400_contains root400_contains (c:=root800) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid801_contains : mid801.Contains (rootPhase 800) := root800_contains
lemma root801_contains : root801.Contains (rootPhase 801) := by
  have hh := CBox.mul_contains_e mid801_contains root1_contains (c:=root801) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root802_contains : root802.Contains (rootPhase 802) := by
  have hh := CBox.mul_contains_e root401_contains root401_contains (c:=root802) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid803_contains : mid803.Contains (rootPhase 802) := root802_contains
lemma root803_contains : root803.Contains (rootPhase 803) := by
  have hh := CBox.mul_contains_e mid803_contains root1_contains (c:=root803) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root804_contains : root804.Contains (rootPhase 804) := by
  have hh := CBox.mul_contains_e root402_contains root402_contains (c:=root804) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid805_contains : mid805.Contains (rootPhase 804) := root804_contains
lemma root805_contains : root805.Contains (rootPhase 805) := by
  have hh := CBox.mul_contains_e mid805_contains root1_contains (c:=root805) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root806_contains : root806.Contains (rootPhase 806) := by
  have hh := CBox.mul_contains_e root403_contains root403_contains (c:=root806) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid807_contains : mid807.Contains (rootPhase 806) := root806_contains
lemma root807_contains : root807.Contains (rootPhase 807) := by
  have hh := CBox.mul_contains_e mid807_contains root1_contains (c:=root807) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root808_contains : root808.Contains (rootPhase 808) := by
  have hh := CBox.mul_contains_e root404_contains root404_contains (c:=root808) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid809_contains : mid809.Contains (rootPhase 808) := root808_contains
lemma root809_contains : root809.Contains (rootPhase 809) := by
  have hh := CBox.mul_contains_e mid809_contains root1_contains (c:=root809) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root810_contains : root810.Contains (rootPhase 810) := by
  have hh := CBox.mul_contains_e root405_contains root405_contains (c:=root810) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid811_contains : mid811.Contains (rootPhase 810) := root810_contains
lemma root811_contains : root811.Contains (rootPhase 811) := by
  have hh := CBox.mul_contains_e mid811_contains root1_contains (c:=root811) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root812_contains : root812.Contains (rootPhase 812) := by
  have hh := CBox.mul_contains_e root406_contains root406_contains (c:=root812) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid813_contains : mid813.Contains (rootPhase 812) := root812_contains
lemma root813_contains : root813.Contains (rootPhase 813) := by
  have hh := CBox.mul_contains_e mid813_contains root1_contains (c:=root813) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root814_contains : root814.Contains (rootPhase 814) := by
  have hh := CBox.mul_contains_e root407_contains root407_contains (c:=root814) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid815_contains : mid815.Contains (rootPhase 814) := root814_contains
lemma root815_contains : root815.Contains (rootPhase 815) := by
  have hh := CBox.mul_contains_e mid815_contains root1_contains (c:=root815) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root816_contains : root816.Contains (rootPhase 816) := by
  have hh := CBox.mul_contains_e root408_contains root408_contains (c:=root816) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid817_contains : mid817.Contains (rootPhase 816) := root816_contains
lemma root817_contains : root817.Contains (rootPhase 817) := by
  have hh := CBox.mul_contains_e mid817_contains root1_contains (c:=root817) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root818_contains : root818.Contains (rootPhase 818) := by
  have hh := CBox.mul_contains_e root409_contains root409_contains (c:=root818) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid819_contains : mid819.Contains (rootPhase 818) := root818_contains
lemma root819_contains : root819.Contains (rootPhase 819) := by
  have hh := CBox.mul_contains_e mid819_contains root1_contains (c:=root819) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root820_contains : root820.Contains (rootPhase 820) := by
  have hh := CBox.mul_contains_e root410_contains root410_contains (c:=root820) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid821_contains : mid821.Contains (rootPhase 820) := root820_contains
lemma root821_contains : root821.Contains (rootPhase 821) := by
  have hh := CBox.mul_contains_e mid821_contains root1_contains (c:=root821) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root822_contains : root822.Contains (rootPhase 822) := by
  have hh := CBox.mul_contains_e root411_contains root411_contains (c:=root822) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid823_contains : mid823.Contains (rootPhase 822) := root822_contains
lemma root823_contains : root823.Contains (rootPhase 823) := by
  have hh := CBox.mul_contains_e mid823_contains root1_contains (c:=root823) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root824_contains : root824.Contains (rootPhase 824) := by
  have hh := CBox.mul_contains_e root412_contains root412_contains (c:=root824) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid825_contains : mid825.Contains (rootPhase 824) := root824_contains
lemma root825_contains : root825.Contains (rootPhase 825) := by
  have hh := CBox.mul_contains_e mid825_contains root1_contains (c:=root825) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root826_contains : root826.Contains (rootPhase 826) := by
  have hh := CBox.mul_contains_e root413_contains root413_contains (c:=root826) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid827_contains : mid827.Contains (rootPhase 826) := root826_contains
lemma root827_contains : root827.Contains (rootPhase 827) := by
  have hh := CBox.mul_contains_e mid827_contains root1_contains (c:=root827) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root828_contains : root828.Contains (rootPhase 828) := by
  have hh := CBox.mul_contains_e root414_contains root414_contains (c:=root828) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid829_contains : mid829.Contains (rootPhase 828) := root828_contains
lemma root829_contains : root829.Contains (rootPhase 829) := by
  have hh := CBox.mul_contains_e mid829_contains root1_contains (c:=root829) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root830_contains : root830.Contains (rootPhase 830) := by
  have hh := CBox.mul_contains_e root415_contains root415_contains (c:=root830) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid831_contains : mid831.Contains (rootPhase 830) := root830_contains
lemma root831_contains : root831.Contains (rootPhase 831) := by
  have hh := CBox.mul_contains_e mid831_contains root1_contains (c:=root831) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root832_contains : root832.Contains (rootPhase 832) := by
  have hh := CBox.mul_contains_e root416_contains root416_contains (c:=root832) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid833_contains : mid833.Contains (rootPhase 832) := root832_contains
lemma root833_contains : root833.Contains (rootPhase 833) := by
  have hh := CBox.mul_contains_e mid833_contains root1_contains (c:=root833) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root834_contains : root834.Contains (rootPhase 834) := by
  have hh := CBox.mul_contains_e root417_contains root417_contains (c:=root834) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid835_contains : mid835.Contains (rootPhase 834) := root834_contains
lemma root835_contains : root835.Contains (rootPhase 835) := by
  have hh := CBox.mul_contains_e mid835_contains root1_contains (c:=root835) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root836_contains : root836.Contains (rootPhase 836) := by
  have hh := CBox.mul_contains_e root418_contains root418_contains (c:=root836) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid837_contains : mid837.Contains (rootPhase 836) := root836_contains
lemma root837_contains : root837.Contains (rootPhase 837) := by
  have hh := CBox.mul_contains_e mid837_contains root1_contains (c:=root837) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root838_contains : root838.Contains (rootPhase 838) := by
  have hh := CBox.mul_contains_e root419_contains root419_contains (c:=root838) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid839_contains : mid839.Contains (rootPhase 838) := root838_contains
lemma root839_contains : root839.Contains (rootPhase 839) := by
  have hh := CBox.mul_contains_e mid839_contains root1_contains (c:=root839) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root840_contains : root840.Contains (rootPhase 840) := by
  have hh := CBox.mul_contains_e root420_contains root420_contains (c:=root840) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid841_contains : mid841.Contains (rootPhase 840) := root840_contains
lemma root841_contains : root841.Contains (rootPhase 841) := by
  have hh := CBox.mul_contains_e mid841_contains root1_contains (c:=root841) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root842_contains : root842.Contains (rootPhase 842) := by
  have hh := CBox.mul_contains_e root421_contains root421_contains (c:=root842) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid843_contains : mid843.Contains (rootPhase 842) := root842_contains
lemma root843_contains : root843.Contains (rootPhase 843) := by
  have hh := CBox.mul_contains_e mid843_contains root1_contains (c:=root843) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root844_contains : root844.Contains (rootPhase 844) := by
  have hh := CBox.mul_contains_e root422_contains root422_contains (c:=root844) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid845_contains : mid845.Contains (rootPhase 844) := root844_contains
lemma root845_contains : root845.Contains (rootPhase 845) := by
  have hh := CBox.mul_contains_e mid845_contains root1_contains (c:=root845) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root846_contains : root846.Contains (rootPhase 846) := by
  have hh := CBox.mul_contains_e root423_contains root423_contains (c:=root846) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid847_contains : mid847.Contains (rootPhase 846) := root846_contains
lemma root847_contains : root847.Contains (rootPhase 847) := by
  have hh := CBox.mul_contains_e mid847_contains root1_contains (c:=root847) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root848_contains : root848.Contains (rootPhase 848) := by
  have hh := CBox.mul_contains_e root424_contains root424_contains (c:=root848) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid849_contains : mid849.Contains (rootPhase 848) := root848_contains
lemma root849_contains : root849.Contains (rootPhase 849) := by
  have hh := CBox.mul_contains_e mid849_contains root1_contains (c:=root849) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root850_contains : root850.Contains (rootPhase 850) := by
  have hh := CBox.mul_contains_e root425_contains root425_contains (c:=root850) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid851_contains : mid851.Contains (rootPhase 850) := root850_contains
lemma root851_contains : root851.Contains (rootPhase 851) := by
  have hh := CBox.mul_contains_e mid851_contains root1_contains (c:=root851) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root852_contains : root852.Contains (rootPhase 852) := by
  have hh := CBox.mul_contains_e root426_contains root426_contains (c:=root852) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid853_contains : mid853.Contains (rootPhase 852) := root852_contains
lemma root853_contains : root853.Contains (rootPhase 853) := by
  have hh := CBox.mul_contains_e mid853_contains root1_contains (c:=root853) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root854_contains : root854.Contains (rootPhase 854) := by
  have hh := CBox.mul_contains_e root427_contains root427_contains (c:=root854) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid855_contains : mid855.Contains (rootPhase 854) := root854_contains
lemma root855_contains : root855.Contains (rootPhase 855) := by
  have hh := CBox.mul_contains_e mid855_contains root1_contains (c:=root855) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root856_contains : root856.Contains (rootPhase 856) := by
  have hh := CBox.mul_contains_e root428_contains root428_contains (c:=root856) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid857_contains : mid857.Contains (rootPhase 856) := root856_contains
lemma root857_contains : root857.Contains (rootPhase 857) := by
  have hh := CBox.mul_contains_e mid857_contains root1_contains (c:=root857) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root858_contains : root858.Contains (rootPhase 858) := by
  have hh := CBox.mul_contains_e root429_contains root429_contains (c:=root858) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid859_contains : mid859.Contains (rootPhase 858) := root858_contains
lemma root859_contains : root859.Contains (rootPhase 859) := by
  have hh := CBox.mul_contains_e mid859_contains root1_contains (c:=root859) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root860_contains : root860.Contains (rootPhase 860) := by
  have hh := CBox.mul_contains_e root430_contains root430_contains (c:=root860) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid861_contains : mid861.Contains (rootPhase 860) := root860_contains
lemma root861_contains : root861.Contains (rootPhase 861) := by
  have hh := CBox.mul_contains_e mid861_contains root1_contains (c:=root861) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root862_contains : root862.Contains (rootPhase 862) := by
  have hh := CBox.mul_contains_e root431_contains root431_contains (c:=root862) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid863_contains : mid863.Contains (rootPhase 862) := root862_contains
lemma root863_contains : root863.Contains (rootPhase 863) := by
  have hh := CBox.mul_contains_e mid863_contains root1_contains (c:=root863) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root864_contains : root864.Contains (rootPhase 864) := by
  have hh := CBox.mul_contains_e root432_contains root432_contains (c:=root864) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid865_contains : mid865.Contains (rootPhase 864) := root864_contains
lemma root865_contains : root865.Contains (rootPhase 865) := by
  have hh := CBox.mul_contains_e mid865_contains root1_contains (c:=root865) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root866_contains : root866.Contains (rootPhase 866) := by
  have hh := CBox.mul_contains_e root433_contains root433_contains (c:=root866) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid867_contains : mid867.Contains (rootPhase 866) := root866_contains
lemma root867_contains : root867.Contains (rootPhase 867) := by
  have hh := CBox.mul_contains_e mid867_contains root1_contains (c:=root867) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root868_contains : root868.Contains (rootPhase 868) := by
  have hh := CBox.mul_contains_e root434_contains root434_contains (c:=root868) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid869_contains : mid869.Contains (rootPhase 868) := root868_contains
lemma root869_contains : root869.Contains (rootPhase 869) := by
  have hh := CBox.mul_contains_e mid869_contains root1_contains (c:=root869) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root870_contains : root870.Contains (rootPhase 870) := by
  have hh := CBox.mul_contains_e root435_contains root435_contains (c:=root870) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid871_contains : mid871.Contains (rootPhase 870) := root870_contains
lemma root871_contains : root871.Contains (rootPhase 871) := by
  have hh := CBox.mul_contains_e mid871_contains root1_contains (c:=root871) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root872_contains : root872.Contains (rootPhase 872) := by
  have hh := CBox.mul_contains_e root436_contains root436_contains (c:=root872) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid873_contains : mid873.Contains (rootPhase 872) := root872_contains
lemma root873_contains : root873.Contains (rootPhase 873) := by
  have hh := CBox.mul_contains_e mid873_contains root1_contains (c:=root873) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root874_contains : root874.Contains (rootPhase 874) := by
  have hh := CBox.mul_contains_e root437_contains root437_contains (c:=root874) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid875_contains : mid875.Contains (rootPhase 874) := root874_contains
lemma root875_contains : root875.Contains (rootPhase 875) := by
  have hh := CBox.mul_contains_e mid875_contains root1_contains (c:=root875) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root876_contains : root876.Contains (rootPhase 876) := by
  have hh := CBox.mul_contains_e root438_contains root438_contains (c:=root876) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid877_contains : mid877.Contains (rootPhase 876) := root876_contains
lemma root877_contains : root877.Contains (rootPhase 877) := by
  have hh := CBox.mul_contains_e mid877_contains root1_contains (c:=root877) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root878_contains : root878.Contains (rootPhase 878) := by
  have hh := CBox.mul_contains_e root439_contains root439_contains (c:=root878) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid879_contains : mid879.Contains (rootPhase 878) := root878_contains
lemma root879_contains : root879.Contains (rootPhase 879) := by
  have hh := CBox.mul_contains_e mid879_contains root1_contains (c:=root879) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root880_contains : root880.Contains (rootPhase 880) := by
  have hh := CBox.mul_contains_e root440_contains root440_contains (c:=root880) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid881_contains : mid881.Contains (rootPhase 880) := root880_contains
lemma root881_contains : root881.Contains (rootPhase 881) := by
  have hh := CBox.mul_contains_e mid881_contains root1_contains (c:=root881) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root882_contains : root882.Contains (rootPhase 882) := by
  have hh := CBox.mul_contains_e root441_contains root441_contains (c:=root882) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid883_contains : mid883.Contains (rootPhase 882) := root882_contains
lemma root883_contains : root883.Contains (rootPhase 883) := by
  have hh := CBox.mul_contains_e mid883_contains root1_contains (c:=root883) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root884_contains : root884.Contains (rootPhase 884) := by
  have hh := CBox.mul_contains_e root442_contains root442_contains (c:=root884) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid885_contains : mid885.Contains (rootPhase 884) := root884_contains
lemma root885_contains : root885.Contains (rootPhase 885) := by
  have hh := CBox.mul_contains_e mid885_contains root1_contains (c:=root885) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root886_contains : root886.Contains (rootPhase 886) := by
  have hh := CBox.mul_contains_e root443_contains root443_contains (c:=root886) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid887_contains : mid887.Contains (rootPhase 886) := root886_contains
lemma root887_contains : root887.Contains (rootPhase 887) := by
  have hh := CBox.mul_contains_e mid887_contains root1_contains (c:=root887) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root888_contains : root888.Contains (rootPhase 888) := by
  have hh := CBox.mul_contains_e root444_contains root444_contains (c:=root888) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid889_contains : mid889.Contains (rootPhase 888) := root888_contains
lemma root889_contains : root889.Contains (rootPhase 889) := by
  have hh := CBox.mul_contains_e mid889_contains root1_contains (c:=root889) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root890_contains : root890.Contains (rootPhase 890) := by
  have hh := CBox.mul_contains_e root445_contains root445_contains (c:=root890) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid891_contains : mid891.Contains (rootPhase 890) := root890_contains
lemma root891_contains : root891.Contains (rootPhase 891) := by
  have hh := CBox.mul_contains_e mid891_contains root1_contains (c:=root891) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root892_contains : root892.Contains (rootPhase 892) := by
  have hh := CBox.mul_contains_e root446_contains root446_contains (c:=root892) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid893_contains : mid893.Contains (rootPhase 892) := root892_contains
lemma root893_contains : root893.Contains (rootPhase 893) := by
  have hh := CBox.mul_contains_e mid893_contains root1_contains (c:=root893) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root894_contains : root894.Contains (rootPhase 894) := by
  have hh := CBox.mul_contains_e root447_contains root447_contains (c:=root894) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid895_contains : mid895.Contains (rootPhase 894) := root894_contains
lemma root895_contains : root895.Contains (rootPhase 895) := by
  have hh := CBox.mul_contains_e mid895_contains root1_contains (c:=root895) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root896_contains : root896.Contains (rootPhase 896) := by
  have hh := CBox.mul_contains_e root448_contains root448_contains (c:=root896) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid897_contains : mid897.Contains (rootPhase 896) := root896_contains
lemma root897_contains : root897.Contains (rootPhase 897) := by
  have hh := CBox.mul_contains_e mid897_contains root1_contains (c:=root897) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root898_contains : root898.Contains (rootPhase 898) := by
  have hh := CBox.mul_contains_e root449_contains root449_contains (c:=root898) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid899_contains : mid899.Contains (rootPhase 898) := root898_contains
lemma root899_contains : root899.Contains (rootPhase 899) := by
  have hh := CBox.mul_contains_e mid899_contains root1_contains (c:=root899) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root900_contains : root900.Contains (rootPhase 900) := by
  have hh := CBox.mul_contains_e root450_contains root450_contains (c:=root900) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid901_contains : mid901.Contains (rootPhase 900) := root900_contains
lemma root901_contains : root901.Contains (rootPhase 901) := by
  have hh := CBox.mul_contains_e mid901_contains root1_contains (c:=root901) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root902_contains : root902.Contains (rootPhase 902) := by
  have hh := CBox.mul_contains_e root451_contains root451_contains (c:=root902) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid903_contains : mid903.Contains (rootPhase 902) := root902_contains
lemma root903_contains : root903.Contains (rootPhase 903) := by
  have hh := CBox.mul_contains_e mid903_contains root1_contains (c:=root903) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root904_contains : root904.Contains (rootPhase 904) := by
  have hh := CBox.mul_contains_e root452_contains root452_contains (c:=root904) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid905_contains : mid905.Contains (rootPhase 904) := root904_contains
lemma root905_contains : root905.Contains (rootPhase 905) := by
  have hh := CBox.mul_contains_e mid905_contains root1_contains (c:=root905) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root906_contains : root906.Contains (rootPhase 906) := by
  have hh := CBox.mul_contains_e root453_contains root453_contains (c:=root906) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid907_contains : mid907.Contains (rootPhase 906) := root906_contains
lemma root907_contains : root907.Contains (rootPhase 907) := by
  have hh := CBox.mul_contains_e mid907_contains root1_contains (c:=root907) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root908_contains : root908.Contains (rootPhase 908) := by
  have hh := CBox.mul_contains_e root454_contains root454_contains (c:=root908) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid909_contains : mid909.Contains (rootPhase 908) := root908_contains
lemma root909_contains : root909.Contains (rootPhase 909) := by
  have hh := CBox.mul_contains_e mid909_contains root1_contains (c:=root909) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root910_contains : root910.Contains (rootPhase 910) := by
  have hh := CBox.mul_contains_e root455_contains root455_contains (c:=root910) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid911_contains : mid911.Contains (rootPhase 910) := root910_contains
lemma root911_contains : root911.Contains (rootPhase 911) := by
  have hh := CBox.mul_contains_e mid911_contains root1_contains (c:=root911) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root912_contains : root912.Contains (rootPhase 912) := by
  have hh := CBox.mul_contains_e root456_contains root456_contains (c:=root912) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid913_contains : mid913.Contains (rootPhase 912) := root912_contains
lemma root913_contains : root913.Contains (rootPhase 913) := by
  have hh := CBox.mul_contains_e mid913_contains root1_contains (c:=root913) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root914_contains : root914.Contains (rootPhase 914) := by
  have hh := CBox.mul_contains_e root457_contains root457_contains (c:=root914) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid915_contains : mid915.Contains (rootPhase 914) := root914_contains
lemma root915_contains : root915.Contains (rootPhase 915) := by
  have hh := CBox.mul_contains_e mid915_contains root1_contains (c:=root915) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root916_contains : root916.Contains (rootPhase 916) := by
  have hh := CBox.mul_contains_e root458_contains root458_contains (c:=root916) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid917_contains : mid917.Contains (rootPhase 916) := root916_contains
lemma root917_contains : root917.Contains (rootPhase 917) := by
  have hh := CBox.mul_contains_e mid917_contains root1_contains (c:=root917) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root918_contains : root918.Contains (rootPhase 918) := by
  have hh := CBox.mul_contains_e root459_contains root459_contains (c:=root918) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid919_contains : mid919.Contains (rootPhase 918) := root918_contains
lemma root919_contains : root919.Contains (rootPhase 919) := by
  have hh := CBox.mul_contains_e mid919_contains root1_contains (c:=root919) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root920_contains : root920.Contains (rootPhase 920) := by
  have hh := CBox.mul_contains_e root460_contains root460_contains (c:=root920) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid921_contains : mid921.Contains (rootPhase 920) := root920_contains
lemma root921_contains : root921.Contains (rootPhase 921) := by
  have hh := CBox.mul_contains_e mid921_contains root1_contains (c:=root921) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root922_contains : root922.Contains (rootPhase 922) := by
  have hh := CBox.mul_contains_e root461_contains root461_contains (c:=root922) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid923_contains : mid923.Contains (rootPhase 922) := root922_contains
lemma root923_contains : root923.Contains (rootPhase 923) := by
  have hh := CBox.mul_contains_e mid923_contains root1_contains (c:=root923) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root924_contains : root924.Contains (rootPhase 924) := by
  have hh := CBox.mul_contains_e root462_contains root462_contains (c:=root924) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid925_contains : mid925.Contains (rootPhase 924) := root924_contains
lemma root925_contains : root925.Contains (rootPhase 925) := by
  have hh := CBox.mul_contains_e mid925_contains root1_contains (c:=root925) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root926_contains : root926.Contains (rootPhase 926) := by
  have hh := CBox.mul_contains_e root463_contains root463_contains (c:=root926) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid927_contains : mid927.Contains (rootPhase 926) := root926_contains
lemma root927_contains : root927.Contains (rootPhase 927) := by
  have hh := CBox.mul_contains_e mid927_contains root1_contains (c:=root927) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root928_contains : root928.Contains (rootPhase 928) := by
  have hh := CBox.mul_contains_e root464_contains root464_contains (c:=root928) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid929_contains : mid929.Contains (rootPhase 928) := root928_contains
lemma root929_contains : root929.Contains (rootPhase 929) := by
  have hh := CBox.mul_contains_e mid929_contains root1_contains (c:=root929) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root930_contains : root930.Contains (rootPhase 930) := by
  have hh := CBox.mul_contains_e root465_contains root465_contains (c:=root930) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid931_contains : mid931.Contains (rootPhase 930) := root930_contains
lemma root931_contains : root931.Contains (rootPhase 931) := by
  have hh := CBox.mul_contains_e mid931_contains root1_contains (c:=root931) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root932_contains : root932.Contains (rootPhase 932) := by
  have hh := CBox.mul_contains_e root466_contains root466_contains (c:=root932) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid933_contains : mid933.Contains (rootPhase 932) := root932_contains
lemma root933_contains : root933.Contains (rootPhase 933) := by
  have hh := CBox.mul_contains_e mid933_contains root1_contains (c:=root933) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root934_contains : root934.Contains (rootPhase 934) := by
  have hh := CBox.mul_contains_e root467_contains root467_contains (c:=root934) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid935_contains : mid935.Contains (rootPhase 934) := root934_contains
lemma root935_contains : root935.Contains (rootPhase 935) := by
  have hh := CBox.mul_contains_e mid935_contains root1_contains (c:=root935) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root936_contains : root936.Contains (rootPhase 936) := by
  have hh := CBox.mul_contains_e root468_contains root468_contains (c:=root936) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid937_contains : mid937.Contains (rootPhase 936) := root936_contains
lemma root937_contains : root937.Contains (rootPhase 937) := by
  have hh := CBox.mul_contains_e mid937_contains root1_contains (c:=root937) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root938_contains : root938.Contains (rootPhase 938) := by
  have hh := CBox.mul_contains_e root469_contains root469_contains (c:=root938) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid939_contains : mid939.Contains (rootPhase 938) := root938_contains
lemma root939_contains : root939.Contains (rootPhase 939) := by
  have hh := CBox.mul_contains_e mid939_contains root1_contains (c:=root939) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root940_contains : root940.Contains (rootPhase 940) := by
  have hh := CBox.mul_contains_e root470_contains root470_contains (c:=root940) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid941_contains : mid941.Contains (rootPhase 940) := root940_contains
lemma root941_contains : root941.Contains (rootPhase 941) := by
  have hh := CBox.mul_contains_e mid941_contains root1_contains (c:=root941) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root942_contains : root942.Contains (rootPhase 942) := by
  have hh := CBox.mul_contains_e root471_contains root471_contains (c:=root942) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid943_contains : mid943.Contains (rootPhase 942) := root942_contains
lemma root943_contains : root943.Contains (rootPhase 943) := by
  have hh := CBox.mul_contains_e mid943_contains root1_contains (c:=root943) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root944_contains : root944.Contains (rootPhase 944) := by
  have hh := CBox.mul_contains_e root472_contains root472_contains (c:=root944) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid945_contains : mid945.Contains (rootPhase 944) := root944_contains
lemma root945_contains : root945.Contains (rootPhase 945) := by
  have hh := CBox.mul_contains_e mid945_contains root1_contains (c:=root945) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root946_contains : root946.Contains (rootPhase 946) := by
  have hh := CBox.mul_contains_e root473_contains root473_contains (c:=root946) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid947_contains : mid947.Contains (rootPhase 946) := root946_contains
lemma root947_contains : root947.Contains (rootPhase 947) := by
  have hh := CBox.mul_contains_e mid947_contains root1_contains (c:=root947) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root948_contains : root948.Contains (rootPhase 948) := by
  have hh := CBox.mul_contains_e root474_contains root474_contains (c:=root948) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid949_contains : mid949.Contains (rootPhase 948) := root948_contains
lemma root949_contains : root949.Contains (rootPhase 949) := by
  have hh := CBox.mul_contains_e mid949_contains root1_contains (c:=root949) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root950_contains : root950.Contains (rootPhase 950) := by
  have hh := CBox.mul_contains_e root475_contains root475_contains (c:=root950) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid951_contains : mid951.Contains (rootPhase 950) := root950_contains
lemma root951_contains : root951.Contains (rootPhase 951) := by
  have hh := CBox.mul_contains_e mid951_contains root1_contains (c:=root951) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root952_contains : root952.Contains (rootPhase 952) := by
  have hh := CBox.mul_contains_e root476_contains root476_contains (c:=root952) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid953_contains : mid953.Contains (rootPhase 952) := root952_contains
lemma root953_contains : root953.Contains (rootPhase 953) := by
  have hh := CBox.mul_contains_e mid953_contains root1_contains (c:=root953) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root954_contains : root954.Contains (rootPhase 954) := by
  have hh := CBox.mul_contains_e root477_contains root477_contains (c:=root954) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid955_contains : mid955.Contains (rootPhase 954) := root954_contains
lemma root955_contains : root955.Contains (rootPhase 955) := by
  have hh := CBox.mul_contains_e mid955_contains root1_contains (c:=root955) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root956_contains : root956.Contains (rootPhase 956) := by
  have hh := CBox.mul_contains_e root478_contains root478_contains (c:=root956) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid957_contains : mid957.Contains (rootPhase 956) := root956_contains
lemma root957_contains : root957.Contains (rootPhase 957) := by
  have hh := CBox.mul_contains_e mid957_contains root1_contains (c:=root957) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root958_contains : root958.Contains (rootPhase 958) := by
  have hh := CBox.mul_contains_e root479_contains root479_contains (c:=root958) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid959_contains : mid959.Contains (rootPhase 958) := root958_contains
lemma root959_contains : root959.Contains (rootPhase 959) := by
  have hh := CBox.mul_contains_e mid959_contains root1_contains (c:=root959) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root960_contains : root960.Contains (rootPhase 960) := by
  have hh := CBox.mul_contains_e root480_contains root480_contains (c:=root960) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid961_contains : mid961.Contains (rootPhase 960) := root960_contains
lemma root961_contains : root961.Contains (rootPhase 961) := by
  have hh := CBox.mul_contains_e mid961_contains root1_contains (c:=root961) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root962_contains : root962.Contains (rootPhase 962) := by
  have hh := CBox.mul_contains_e root481_contains root481_contains (c:=root962) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid963_contains : mid963.Contains (rootPhase 962) := root962_contains
lemma root963_contains : root963.Contains (rootPhase 963) := by
  have hh := CBox.mul_contains_e mid963_contains root1_contains (c:=root963) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root964_contains : root964.Contains (rootPhase 964) := by
  have hh := CBox.mul_contains_e root482_contains root482_contains (c:=root964) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid965_contains : mid965.Contains (rootPhase 964) := root964_contains
lemma root965_contains : root965.Contains (rootPhase 965) := by
  have hh := CBox.mul_contains_e mid965_contains root1_contains (c:=root965) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root966_contains : root966.Contains (rootPhase 966) := by
  have hh := CBox.mul_contains_e root483_contains root483_contains (c:=root966) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid967_contains : mid967.Contains (rootPhase 966) := root966_contains
lemma root967_contains : root967.Contains (rootPhase 967) := by
  have hh := CBox.mul_contains_e mid967_contains root1_contains (c:=root967) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root968_contains : root968.Contains (rootPhase 968) := by
  have hh := CBox.mul_contains_e root484_contains root484_contains (c:=root968) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid969_contains : mid969.Contains (rootPhase 968) := root968_contains
lemma root969_contains : root969.Contains (rootPhase 969) := by
  have hh := CBox.mul_contains_e mid969_contains root1_contains (c:=root969) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root970_contains : root970.Contains (rootPhase 970) := by
  have hh := CBox.mul_contains_e root485_contains root485_contains (c:=root970) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid971_contains : mid971.Contains (rootPhase 970) := root970_contains
lemma root971_contains : root971.Contains (rootPhase 971) := by
  have hh := CBox.mul_contains_e mid971_contains root1_contains (c:=root971) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root972_contains : root972.Contains (rootPhase 972) := by
  have hh := CBox.mul_contains_e root486_contains root486_contains (c:=root972) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid973_contains : mid973.Contains (rootPhase 972) := root972_contains
lemma root973_contains : root973.Contains (rootPhase 973) := by
  have hh := CBox.mul_contains_e mid973_contains root1_contains (c:=root973) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root974_contains : root974.Contains (rootPhase 974) := by
  have hh := CBox.mul_contains_e root487_contains root487_contains (c:=root974) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid975_contains : mid975.Contains (rootPhase 974) := root974_contains
lemma root975_contains : root975.Contains (rootPhase 975) := by
  have hh := CBox.mul_contains_e mid975_contains root1_contains (c:=root975) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root976_contains : root976.Contains (rootPhase 976) := by
  have hh := CBox.mul_contains_e root488_contains root488_contains (c:=root976) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid977_contains : mid977.Contains (rootPhase 976) := root976_contains
lemma root977_contains : root977.Contains (rootPhase 977) := by
  have hh := CBox.mul_contains_e mid977_contains root1_contains (c:=root977) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root978_contains : root978.Contains (rootPhase 978) := by
  have hh := CBox.mul_contains_e root489_contains root489_contains (c:=root978) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid979_contains : mid979.Contains (rootPhase 978) := root978_contains
lemma root979_contains : root979.Contains (rootPhase 979) := by
  have hh := CBox.mul_contains_e mid979_contains root1_contains (c:=root979) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root980_contains : root980.Contains (rootPhase 980) := by
  have hh := CBox.mul_contains_e root490_contains root490_contains (c:=root980) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid981_contains : mid981.Contains (rootPhase 980) := root980_contains
lemma root981_contains : root981.Contains (rootPhase 981) := by
  have hh := CBox.mul_contains_e mid981_contains root1_contains (c:=root981) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root982_contains : root982.Contains (rootPhase 982) := by
  have hh := CBox.mul_contains_e root491_contains root491_contains (c:=root982) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid983_contains : mid983.Contains (rootPhase 982) := root982_contains
lemma root983_contains : root983.Contains (rootPhase 983) := by
  have hh := CBox.mul_contains_e mid983_contains root1_contains (c:=root983) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root984_contains : root984.Contains (rootPhase 984) := by
  have hh := CBox.mul_contains_e root492_contains root492_contains (c:=root984) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid985_contains : mid985.Contains (rootPhase 984) := root984_contains
lemma root985_contains : root985.Contains (rootPhase 985) := by
  have hh := CBox.mul_contains_e mid985_contains root1_contains (c:=root985) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root986_contains : root986.Contains (rootPhase 986) := by
  have hh := CBox.mul_contains_e root493_contains root493_contains (c:=root986) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid987_contains : mid987.Contains (rootPhase 986) := root986_contains
lemma root987_contains : root987.Contains (rootPhase 987) := by
  have hh := CBox.mul_contains_e mid987_contains root1_contains (c:=root987) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root988_contains : root988.Contains (rootPhase 988) := by
  have hh := CBox.mul_contains_e root494_contains root494_contains (c:=root988) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid989_contains : mid989.Contains (rootPhase 988) := root988_contains
lemma root989_contains : root989.Contains (rootPhase 989) := by
  have hh := CBox.mul_contains_e mid989_contains root1_contains (c:=root989) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root990_contains : root990.Contains (rootPhase 990) := by
  have hh := CBox.mul_contains_e root495_contains root495_contains (c:=root990) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid991_contains : mid991.Contains (rootPhase 990) := root990_contains
lemma root991_contains : root991.Contains (rootPhase 991) := by
  have hh := CBox.mul_contains_e mid991_contains root1_contains (c:=root991) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root992_contains : root992.Contains (rootPhase 992) := by
  have hh := CBox.mul_contains_e root496_contains root496_contains (c:=root992) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid993_contains : mid993.Contains (rootPhase 992) := root992_contains
lemma root993_contains : root993.Contains (rootPhase 993) := by
  have hh := CBox.mul_contains_e mid993_contains root1_contains (c:=root993) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root994_contains : root994.Contains (rootPhase 994) := by
  have hh := CBox.mul_contains_e root497_contains root497_contains (c:=root994) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid995_contains : mid995.Contains (rootPhase 994) := root994_contains
lemma root995_contains : root995.Contains (rootPhase 995) := by
  have hh := CBox.mul_contains_e mid995_contains root1_contains (c:=root995) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root996_contains : root996.Contains (rootPhase 996) := by
  have hh := CBox.mul_contains_e root498_contains root498_contains (c:=root996) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid997_contains : mid997.Contains (rootPhase 996) := root996_contains
lemma root997_contains : root997.Contains (rootPhase 997) := by
  have hh := CBox.mul_contains_e mid997_contains root1_contains (c:=root997) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root998_contains : root998.Contains (rootPhase 998) := by
  have hh := CBox.mul_contains_e root499_contains root499_contains (c:=root998) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid999_contains : mid999.Contains (rootPhase 998) := root998_contains
lemma root999_contains : root999.Contains (rootPhase 999) := by
  have hh := CBox.mul_contains_e mid999_contains root1_contains (c:=root999) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1000_contains : root1000.Contains (rootPhase 1000) := by
  have hh := CBox.mul_contains_e root500_contains root500_contains (c:=root1000) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1001_contains : mid1001.Contains (rootPhase 1000) := root1000_contains
lemma root1001_contains : root1001.Contains (rootPhase 1001) := by
  have hh := CBox.mul_contains_e mid1001_contains root1_contains (c:=root1001) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1002_contains : root1002.Contains (rootPhase 1002) := by
  have hh := CBox.mul_contains_e root501_contains root501_contains (c:=root1002) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1003_contains : mid1003.Contains (rootPhase 1002) := root1002_contains
lemma root1003_contains : root1003.Contains (rootPhase 1003) := by
  have hh := CBox.mul_contains_e mid1003_contains root1_contains (c:=root1003) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1004_contains : root1004.Contains (rootPhase 1004) := by
  have hh := CBox.mul_contains_e root502_contains root502_contains (c:=root1004) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1005_contains : mid1005.Contains (rootPhase 1004) := root1004_contains
lemma root1005_contains : root1005.Contains (rootPhase 1005) := by
  have hh := CBox.mul_contains_e mid1005_contains root1_contains (c:=root1005) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1006_contains : root1006.Contains (rootPhase 1006) := by
  have hh := CBox.mul_contains_e root503_contains root503_contains (c:=root1006) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1007_contains : mid1007.Contains (rootPhase 1006) := root1006_contains
lemma root1007_contains : root1007.Contains (rootPhase 1007) := by
  have hh := CBox.mul_contains_e mid1007_contains root1_contains (c:=root1007) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1008_contains : root1008.Contains (rootPhase 1008) := by
  have hh := CBox.mul_contains_e root504_contains root504_contains (c:=root1008) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1009_contains : mid1009.Contains (rootPhase 1008) := root1008_contains
lemma root1009_contains : root1009.Contains (rootPhase 1009) := by
  have hh := CBox.mul_contains_e mid1009_contains root1_contains (c:=root1009) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1010_contains : root1010.Contains (rootPhase 1010) := by
  have hh := CBox.mul_contains_e root505_contains root505_contains (c:=root1010) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1011_contains : mid1011.Contains (rootPhase 1010) := root1010_contains
lemma root1011_contains : root1011.Contains (rootPhase 1011) := by
  have hh := CBox.mul_contains_e mid1011_contains root1_contains (c:=root1011) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1012_contains : root1012.Contains (rootPhase 1012) := by
  have hh := CBox.mul_contains_e root506_contains root506_contains (c:=root1012) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1013_contains : mid1013.Contains (rootPhase 1012) := root1012_contains
lemma root1013_contains : root1013.Contains (rootPhase 1013) := by
  have hh := CBox.mul_contains_e mid1013_contains root1_contains (c:=root1013) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1014_contains : root1014.Contains (rootPhase 1014) := by
  have hh := CBox.mul_contains_e root507_contains root507_contains (c:=root1014) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1015_contains : mid1015.Contains (rootPhase 1014) := root1014_contains
lemma root1015_contains : root1015.Contains (rootPhase 1015) := by
  have hh := CBox.mul_contains_e mid1015_contains root1_contains (c:=root1015) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1016_contains : root1016.Contains (rootPhase 1016) := by
  have hh := CBox.mul_contains_e root508_contains root508_contains (c:=root1016) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1017_contains : mid1017.Contains (rootPhase 1016) := root1016_contains
lemma root1017_contains : root1017.Contains (rootPhase 1017) := by
  have hh := CBox.mul_contains_e mid1017_contains root1_contains (c:=root1017) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1018_contains : root1018.Contains (rootPhase 1018) := by
  have hh := CBox.mul_contains_e root509_contains root509_contains (c:=root1018) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1019_contains : mid1019.Contains (rootPhase 1018) := root1018_contains
lemma root1019_contains : root1019.Contains (rootPhase 1019) := by
  have hh := CBox.mul_contains_e mid1019_contains root1_contains (c:=root1019) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1020_contains : root1020.Contains (rootPhase 1020) := by
  have hh := CBox.mul_contains_e root510_contains root510_contains (c:=root1020) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1021_contains : mid1021.Contains (rootPhase 1020) := root1020_contains
lemma root1021_contains : root1021.Contains (rootPhase 1021) := by
  have hh := CBox.mul_contains_e mid1021_contains root1_contains (c:=root1021) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma root1022_contains : root1022.Contains (rootPhase 1022) := by
  have hh := CBox.mul_contains_e root511_contains root511_contains (c:=root1022) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
lemma mid1023_contains : mid1023.Contains (rootPhase 1022) := root1022_contains
lemma root1023_contains : root1023.Contains (rootPhase 1023) := by
  have hh := CBox.mul_contains_e mid1023_contains root1_contains (c:=root1023) (by decide +kernel)
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
lemma roots13_contains (j : Fin 32) : (roots13 j).Contains (rootPhase (416+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root416_contains
  · exact IntegerRoots.root417_contains
  · exact IntegerRoots.root418_contains
  · exact IntegerRoots.root419_contains
  · exact IntegerRoots.root420_contains
  · exact IntegerRoots.root421_contains
  · exact IntegerRoots.root422_contains
  · exact IntegerRoots.root423_contains
  · exact IntegerRoots.root424_contains
  · exact IntegerRoots.root425_contains
  · exact IntegerRoots.root426_contains
  · exact IntegerRoots.root427_contains
  · exact IntegerRoots.root428_contains
  · exact IntegerRoots.root429_contains
  · exact IntegerRoots.root430_contains
  · exact IntegerRoots.root431_contains
  · exact IntegerRoots.root432_contains
  · exact IntegerRoots.root433_contains
  · exact IntegerRoots.root434_contains
  · exact IntegerRoots.root435_contains
  · exact IntegerRoots.root436_contains
  · exact IntegerRoots.root437_contains
  · exact IntegerRoots.root438_contains
  · exact IntegerRoots.root439_contains
  · exact IntegerRoots.root440_contains
  · exact IntegerRoots.root441_contains
  · exact IntegerRoots.root442_contains
  · exact IntegerRoots.root443_contains
  · exact IntegerRoots.root444_contains
  · exact IntegerRoots.root445_contains
  · exact IntegerRoots.root446_contains
  · exact IntegerRoots.root447_contains
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
lemma roots15_contains (j : Fin 32) : (roots15 j).Contains (rootPhase (480+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root480_contains
  · exact IntegerRoots.root481_contains
  · exact IntegerRoots.root482_contains
  · exact IntegerRoots.root483_contains
  · exact IntegerRoots.root484_contains
  · exact IntegerRoots.root485_contains
  · exact IntegerRoots.root486_contains
  · exact IntegerRoots.root487_contains
  · exact IntegerRoots.root488_contains
  · exact IntegerRoots.root489_contains
  · exact IntegerRoots.root490_contains
  · exact IntegerRoots.root491_contains
  · exact IntegerRoots.root492_contains
  · exact IntegerRoots.root493_contains
  · exact IntegerRoots.root494_contains
  · exact IntegerRoots.root495_contains
  · exact IntegerRoots.root496_contains
  · exact IntegerRoots.root497_contains
  · exact IntegerRoots.root498_contains
  · exact IntegerRoots.root499_contains
  · exact IntegerRoots.root500_contains
  · exact IntegerRoots.root501_contains
  · exact IntegerRoots.root502_contains
  · exact IntegerRoots.root503_contains
  · exact IntegerRoots.root504_contains
  · exact IntegerRoots.root505_contains
  · exact IntegerRoots.root506_contains
  · exact IntegerRoots.root507_contains
  · exact IntegerRoots.root508_contains
  · exact IntegerRoots.root509_contains
  · exact IntegerRoots.root510_contains
  · exact IntegerRoots.root511_contains
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
lemma roots17_contains (j : Fin 32) : (roots17 j).Contains (rootPhase (544+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root544_contains
  · exact IntegerRoots.root545_contains
  · exact IntegerRoots.root546_contains
  · exact IntegerRoots.root547_contains
  · exact IntegerRoots.root548_contains
  · exact IntegerRoots.root549_contains
  · exact IntegerRoots.root550_contains
  · exact IntegerRoots.root551_contains
  · exact IntegerRoots.root552_contains
  · exact IntegerRoots.root553_contains
  · exact IntegerRoots.root554_contains
  · exact IntegerRoots.root555_contains
  · exact IntegerRoots.root556_contains
  · exact IntegerRoots.root557_contains
  · exact IntegerRoots.root558_contains
  · exact IntegerRoots.root559_contains
  · exact IntegerRoots.root560_contains
  · exact IntegerRoots.root561_contains
  · exact IntegerRoots.root562_contains
  · exact IntegerRoots.root563_contains
  · exact IntegerRoots.root564_contains
  · exact IntegerRoots.root565_contains
  · exact IntegerRoots.root566_contains
  · exact IntegerRoots.root567_contains
  · exact IntegerRoots.root568_contains
  · exact IntegerRoots.root569_contains
  · exact IntegerRoots.root570_contains
  · exact IntegerRoots.root571_contains
  · exact IntegerRoots.root572_contains
  · exact IntegerRoots.root573_contains
  · exact IntegerRoots.root574_contains
  · exact IntegerRoots.root575_contains
lemma roots18_contains (j : Fin 32) : (roots18 j).Contains (rootPhase (576+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root576_contains
  · exact IntegerRoots.root577_contains
  · exact IntegerRoots.root578_contains
  · exact IntegerRoots.root579_contains
  · exact IntegerRoots.root580_contains
  · exact IntegerRoots.root581_contains
  · exact IntegerRoots.root582_contains
  · exact IntegerRoots.root583_contains
  · exact IntegerRoots.root584_contains
  · exact IntegerRoots.root585_contains
  · exact IntegerRoots.root586_contains
  · exact IntegerRoots.root587_contains
  · exact IntegerRoots.root588_contains
  · exact IntegerRoots.root589_contains
  · exact IntegerRoots.root590_contains
  · exact IntegerRoots.root591_contains
  · exact IntegerRoots.root592_contains
  · exact IntegerRoots.root593_contains
  · exact IntegerRoots.root594_contains
  · exact IntegerRoots.root595_contains
  · exact IntegerRoots.root596_contains
  · exact IntegerRoots.root597_contains
  · exact IntegerRoots.root598_contains
  · exact IntegerRoots.root599_contains
  · exact IntegerRoots.root600_contains
  · exact IntegerRoots.root601_contains
  · exact IntegerRoots.root602_contains
  · exact IntegerRoots.root603_contains
  · exact IntegerRoots.root604_contains
  · exact IntegerRoots.root605_contains
  · exact IntegerRoots.root606_contains
  · exact IntegerRoots.root607_contains
lemma roots19_contains (j : Fin 32) : (roots19 j).Contains (rootPhase (608+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root608_contains
  · exact IntegerRoots.root609_contains
  · exact IntegerRoots.root610_contains
  · exact IntegerRoots.root611_contains
  · exact IntegerRoots.root612_contains
  · exact IntegerRoots.root613_contains
  · exact IntegerRoots.root614_contains
  · exact IntegerRoots.root615_contains
  · exact IntegerRoots.root616_contains
  · exact IntegerRoots.root617_contains
  · exact IntegerRoots.root618_contains
  · exact IntegerRoots.root619_contains
  · exact IntegerRoots.root620_contains
  · exact IntegerRoots.root621_contains
  · exact IntegerRoots.root622_contains
  · exact IntegerRoots.root623_contains
  · exact IntegerRoots.root624_contains
  · exact IntegerRoots.root625_contains
  · exact IntegerRoots.root626_contains
  · exact IntegerRoots.root627_contains
  · exact IntegerRoots.root628_contains
  · exact IntegerRoots.root629_contains
  · exact IntegerRoots.root630_contains
  · exact IntegerRoots.root631_contains
  · exact IntegerRoots.root632_contains
  · exact IntegerRoots.root633_contains
  · exact IntegerRoots.root634_contains
  · exact IntegerRoots.root635_contains
  · exact IntegerRoots.root636_contains
  · exact IntegerRoots.root637_contains
  · exact IntegerRoots.root638_contains
  · exact IntegerRoots.root639_contains
lemma roots20_contains (j : Fin 32) : (roots20 j).Contains (rootPhase (640+j.val)) := by
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
lemma roots21_contains (j : Fin 32) : (roots21 j).Contains (rootPhase (672+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root672_contains
  · exact IntegerRoots.root673_contains
  · exact IntegerRoots.root674_contains
  · exact IntegerRoots.root675_contains
  · exact IntegerRoots.root676_contains
  · exact IntegerRoots.root677_contains
  · exact IntegerRoots.root678_contains
  · exact IntegerRoots.root679_contains
  · exact IntegerRoots.root680_contains
  · exact IntegerRoots.root681_contains
  · exact IntegerRoots.root682_contains
  · exact IntegerRoots.root683_contains
  · exact IntegerRoots.root684_contains
  · exact IntegerRoots.root685_contains
  · exact IntegerRoots.root686_contains
  · exact IntegerRoots.root687_contains
  · exact IntegerRoots.root688_contains
  · exact IntegerRoots.root689_contains
  · exact IntegerRoots.root690_contains
  · exact IntegerRoots.root691_contains
  · exact IntegerRoots.root692_contains
  · exact IntegerRoots.root693_contains
  · exact IntegerRoots.root694_contains
  · exact IntegerRoots.root695_contains
  · exact IntegerRoots.root696_contains
  · exact IntegerRoots.root697_contains
  · exact IntegerRoots.root698_contains
  · exact IntegerRoots.root699_contains
  · exact IntegerRoots.root700_contains
  · exact IntegerRoots.root701_contains
  · exact IntegerRoots.root702_contains
  · exact IntegerRoots.root703_contains
lemma roots22_contains (j : Fin 32) : (roots22 j).Contains (rootPhase (704+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root704_contains
  · exact IntegerRoots.root705_contains
  · exact IntegerRoots.root706_contains
  · exact IntegerRoots.root707_contains
  · exact IntegerRoots.root708_contains
  · exact IntegerRoots.root709_contains
  · exact IntegerRoots.root710_contains
  · exact IntegerRoots.root711_contains
  · exact IntegerRoots.root712_contains
  · exact IntegerRoots.root713_contains
  · exact IntegerRoots.root714_contains
  · exact IntegerRoots.root715_contains
  · exact IntegerRoots.root716_contains
  · exact IntegerRoots.root717_contains
  · exact IntegerRoots.root718_contains
  · exact IntegerRoots.root719_contains
  · exact IntegerRoots.root720_contains
  · exact IntegerRoots.root721_contains
  · exact IntegerRoots.root722_contains
  · exact IntegerRoots.root723_contains
  · exact IntegerRoots.root724_contains
  · exact IntegerRoots.root725_contains
  · exact IntegerRoots.root726_contains
  · exact IntegerRoots.root727_contains
  · exact IntegerRoots.root728_contains
  · exact IntegerRoots.root729_contains
  · exact IntegerRoots.root730_contains
  · exact IntegerRoots.root731_contains
  · exact IntegerRoots.root732_contains
  · exact IntegerRoots.root733_contains
  · exact IntegerRoots.root734_contains
  · exact IntegerRoots.root735_contains
lemma roots23_contains (j : Fin 32) : (roots23 j).Contains (rootPhase (736+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root736_contains
  · exact IntegerRoots.root737_contains
  · exact IntegerRoots.root738_contains
  · exact IntegerRoots.root739_contains
  · exact IntegerRoots.root740_contains
  · exact IntegerRoots.root741_contains
  · exact IntegerRoots.root742_contains
  · exact IntegerRoots.root743_contains
  · exact IntegerRoots.root744_contains
  · exact IntegerRoots.root745_contains
  · exact IntegerRoots.root746_contains
  · exact IntegerRoots.root747_contains
  · exact IntegerRoots.root748_contains
  · exact IntegerRoots.root749_contains
  · exact IntegerRoots.root750_contains
  · exact IntegerRoots.root751_contains
  · exact IntegerRoots.root752_contains
  · exact IntegerRoots.root753_contains
  · exact IntegerRoots.root754_contains
  · exact IntegerRoots.root755_contains
  · exact IntegerRoots.root756_contains
  · exact IntegerRoots.root757_contains
  · exact IntegerRoots.root758_contains
  · exact IntegerRoots.root759_contains
  · exact IntegerRoots.root760_contains
  · exact IntegerRoots.root761_contains
  · exact IntegerRoots.root762_contains
  · exact IntegerRoots.root763_contains
  · exact IntegerRoots.root764_contains
  · exact IntegerRoots.root765_contains
  · exact IntegerRoots.root766_contains
  · exact IntegerRoots.root767_contains
lemma roots24_contains (j : Fin 32) : (roots24 j).Contains (rootPhase (768+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root768_contains
  · exact IntegerRoots.root769_contains
  · exact IntegerRoots.root770_contains
  · exact IntegerRoots.root771_contains
  · exact IntegerRoots.root772_contains
  · exact IntegerRoots.root773_contains
  · exact IntegerRoots.root774_contains
  · exact IntegerRoots.root775_contains
  · exact IntegerRoots.root776_contains
  · exact IntegerRoots.root777_contains
  · exact IntegerRoots.root778_contains
  · exact IntegerRoots.root779_contains
  · exact IntegerRoots.root780_contains
  · exact IntegerRoots.root781_contains
  · exact IntegerRoots.root782_contains
  · exact IntegerRoots.root783_contains
  · exact IntegerRoots.root784_contains
  · exact IntegerRoots.root785_contains
  · exact IntegerRoots.root786_contains
  · exact IntegerRoots.root787_contains
  · exact IntegerRoots.root788_contains
  · exact IntegerRoots.root789_contains
  · exact IntegerRoots.root790_contains
  · exact IntegerRoots.root791_contains
  · exact IntegerRoots.root792_contains
  · exact IntegerRoots.root793_contains
  · exact IntegerRoots.root794_contains
  · exact IntegerRoots.root795_contains
  · exact IntegerRoots.root796_contains
  · exact IntegerRoots.root797_contains
  · exact IntegerRoots.root798_contains
  · exact IntegerRoots.root799_contains
lemma roots25_contains (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val)) := by
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
lemma roots26_contains (j : Fin 32) : (roots26 j).Contains (rootPhase (832+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root832_contains
  · exact IntegerRoots.root833_contains
  · exact IntegerRoots.root834_contains
  · exact IntegerRoots.root835_contains
  · exact IntegerRoots.root836_contains
  · exact IntegerRoots.root837_contains
  · exact IntegerRoots.root838_contains
  · exact IntegerRoots.root839_contains
  · exact IntegerRoots.root840_contains
  · exact IntegerRoots.root841_contains
  · exact IntegerRoots.root842_contains
  · exact IntegerRoots.root843_contains
  · exact IntegerRoots.root844_contains
  · exact IntegerRoots.root845_contains
  · exact IntegerRoots.root846_contains
  · exact IntegerRoots.root847_contains
  · exact IntegerRoots.root848_contains
  · exact IntegerRoots.root849_contains
  · exact IntegerRoots.root850_contains
  · exact IntegerRoots.root851_contains
  · exact IntegerRoots.root852_contains
  · exact IntegerRoots.root853_contains
  · exact IntegerRoots.root854_contains
  · exact IntegerRoots.root855_contains
  · exact IntegerRoots.root856_contains
  · exact IntegerRoots.root857_contains
  · exact IntegerRoots.root858_contains
  · exact IntegerRoots.root859_contains
  · exact IntegerRoots.root860_contains
  · exact IntegerRoots.root861_contains
  · exact IntegerRoots.root862_contains
  · exact IntegerRoots.root863_contains
lemma roots27_contains (j : Fin 32) : (roots27 j).Contains (rootPhase (864+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root864_contains
  · exact IntegerRoots.root865_contains
  · exact IntegerRoots.root866_contains
  · exact IntegerRoots.root867_contains
  · exact IntegerRoots.root868_contains
  · exact IntegerRoots.root869_contains
  · exact IntegerRoots.root870_contains
  · exact IntegerRoots.root871_contains
  · exact IntegerRoots.root872_contains
  · exact IntegerRoots.root873_contains
  · exact IntegerRoots.root874_contains
  · exact IntegerRoots.root875_contains
  · exact IntegerRoots.root876_contains
  · exact IntegerRoots.root877_contains
  · exact IntegerRoots.root878_contains
  · exact IntegerRoots.root879_contains
  · exact IntegerRoots.root880_contains
  · exact IntegerRoots.root881_contains
  · exact IntegerRoots.root882_contains
  · exact IntegerRoots.root883_contains
  · exact IntegerRoots.root884_contains
  · exact IntegerRoots.root885_contains
  · exact IntegerRoots.root886_contains
  · exact IntegerRoots.root887_contains
  · exact IntegerRoots.root888_contains
  · exact IntegerRoots.root889_contains
  · exact IntegerRoots.root890_contains
  · exact IntegerRoots.root891_contains
  · exact IntegerRoots.root892_contains
  · exact IntegerRoots.root893_contains
  · exact IntegerRoots.root894_contains
  · exact IntegerRoots.root895_contains
lemma roots28_contains (j : Fin 32) : (roots28 j).Contains (rootPhase (896+j.val)) := by
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
lemma roots29_contains (j : Fin 32) : (roots29 j).Contains (rootPhase (928+j.val)) := by
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
lemma roots30_contains (j : Fin 32) : (roots30 j).Contains (rootPhase (960+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root960_contains
  · exact IntegerRoots.root961_contains
  · exact IntegerRoots.root962_contains
  · exact IntegerRoots.root963_contains
  · exact IntegerRoots.root964_contains
  · exact IntegerRoots.root965_contains
  · exact IntegerRoots.root966_contains
  · exact IntegerRoots.root967_contains
  · exact IntegerRoots.root968_contains
  · exact IntegerRoots.root969_contains
  · exact IntegerRoots.root970_contains
  · exact IntegerRoots.root971_contains
  · exact IntegerRoots.root972_contains
  · exact IntegerRoots.root973_contains
  · exact IntegerRoots.root974_contains
  · exact IntegerRoots.root975_contains
  · exact IntegerRoots.root976_contains
  · exact IntegerRoots.root977_contains
  · exact IntegerRoots.root978_contains
  · exact IntegerRoots.root979_contains
  · exact IntegerRoots.root980_contains
  · exact IntegerRoots.root981_contains
  · exact IntegerRoots.root982_contains
  · exact IntegerRoots.root983_contains
  · exact IntegerRoots.root984_contains
  · exact IntegerRoots.root985_contains
  · exact IntegerRoots.root986_contains
  · exact IntegerRoots.root987_contains
  · exact IntegerRoots.root988_contains
  · exact IntegerRoots.root989_contains
  · exact IntegerRoots.root990_contains
  · exact IntegerRoots.root991_contains
lemma roots31_contains (j : Fin 32) : (roots31 j).Contains (rootPhase (992+j.val)) := by
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
  · exact roots13_contains j
  · exact roots14_contains j
  · exact roots15_contains j
  · exact roots16_contains j
  · exact roots17_contains j
  · exact roots18_contains j
  · exact roots19_contains j
  · exact roots20_contains j
  · exact roots21_contains j
  · exact roots22_contains j
  · exact roots23_contains j
  · exact roots24_contains j
  · exact roots25_contains j
  · exact roots26_contains j
  · exact roots27_contains j
  · exact roots28_contains j
  · exact roots29_contains j
  · exact roots30_contains j
  · exact roots31_contains j
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
  have hh := RBox.contains_add (RBox.contains_rat_e (2*(j:ℤ)+1) 12 (by norm_num))
    (RBox.contains_scale_e (nodeLookup_contains v) 1 12 (by norm_num))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold quadraturePoint
  push_cast
  ring

lemma p3_208_contains : p3_208.Contains (quadraturePoint 3 208) := by
  have ht : p3_208.t.Contains (quadraturePoint 3 208) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨208,by decide⟩).scale 1 12) = p3_208.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨208,by decide⟩
  have he : PointBox.calc p3_208.t = p3_208 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_209_contains : p3_209.Contains (quadraturePoint 3 209) := by
  have ht : p3_209.t.Contains (quadraturePoint 3 209) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨209,by decide⟩).scale 1 12) = p3_209.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨209,by decide⟩
  have he : PointBox.calc p3_209.t = p3_209 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_210_contains : p3_210.Contains (quadraturePoint 3 210) := by
  have ht : p3_210.t.Contains (quadraturePoint 3 210) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨210,by decide⟩).scale 1 12) = p3_210.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨210,by decide⟩
  have he : PointBox.calc p3_210.t = p3_210 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_211_contains : p3_211.Contains (quadraturePoint 3 211) := by
  have ht : p3_211.t.Contains (quadraturePoint 3 211) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨211,by decide⟩).scale 1 12) = p3_211.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨211,by decide⟩
  have he : PointBox.calc p3_211.t = p3_211 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_212_contains : p3_212.Contains (quadraturePoint 3 212) := by
  have ht : p3_212.t.Contains (quadraturePoint 3 212) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨212,by decide⟩).scale 1 12) = p3_212.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨212,by decide⟩
  have he : PointBox.calc p3_212.t = p3_212 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_213_contains : p3_213.Contains (quadraturePoint 3 213) := by
  have ht : p3_213.t.Contains (quadraturePoint 3 213) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨213,by decide⟩).scale 1 12) = p3_213.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨213,by decide⟩
  have he : PointBox.calc p3_213.t = p3_213 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_214_contains : p3_214.Contains (quadraturePoint 3 214) := by
  have ht : p3_214.t.Contains (quadraturePoint 3 214) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨214,by decide⟩).scale 1 12) = p3_214.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨214,by decide⟩
  have he : PointBox.calc p3_214.t = p3_214 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_215_contains : p3_215.Contains (quadraturePoint 3 215) := by
  have ht : p3_215.t.Contains (quadraturePoint 3 215) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨215,by decide⟩).scale 1 12) = p3_215.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨215,by decide⟩
  have he : PointBox.calc p3_215.t = p3_215 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_216_contains : p3_216.Contains (quadraturePoint 3 216) := by
  have ht : p3_216.t.Contains (quadraturePoint 3 216) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨216,by decide⟩).scale 1 12) = p3_216.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨216,by decide⟩
  have he : PointBox.calc p3_216.t = p3_216 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_217_contains : p3_217.Contains (quadraturePoint 3 217) := by
  have ht : p3_217.t.Contains (quadraturePoint 3 217) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨217,by decide⟩).scale 1 12) = p3_217.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨217,by decide⟩
  have he : PointBox.calc p3_217.t = p3_217 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_218_contains : p3_218.Contains (quadraturePoint 3 218) := by
  have ht : p3_218.t.Contains (quadraturePoint 3 218) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨218,by decide⟩).scale 1 12) = p3_218.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨218,by decide⟩
  have he : PointBox.calc p3_218.t = p3_218 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_219_contains : p3_219.Contains (quadraturePoint 3 219) := by
  have ht : p3_219.t.Contains (quadraturePoint 3 219) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨219,by decide⟩).scale 1 12) = p3_219.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨219,by decide⟩
  have he : PointBox.calc p3_219.t = p3_219 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_220_contains : p3_220.Contains (quadraturePoint 3 220) := by
  have ht : p3_220.t.Contains (quadraturePoint 3 220) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨220,by decide⟩).scale 1 12) = p3_220.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨220,by decide⟩
  have he : PointBox.calc p3_220.t = p3_220 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_221_contains : p3_221.Contains (quadraturePoint 3 221) := by
  have ht : p3_221.t.Contains (quadraturePoint 3 221) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨221,by decide⟩).scale 1 12) = p3_221.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨221,by decide⟩
  have he : PointBox.calc p3_221.t = p3_221 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_222_contains : p3_222.Contains (quadraturePoint 3 222) := by
  have ht : p3_222.t.Contains (quadraturePoint 3 222) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨222,by decide⟩).scale 1 12) = p3_222.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨222,by decide⟩
  have he : PointBox.calc p3_222.t = p3_222 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma p3_223_contains : p3_223.Contains (quadraturePoint 3 223) := by
  have ht : p3_223.t.Contains (quadraturePoint 3 223) := by
    have he : (RBox.rat 7 12).add ((nodeLookup ⟨223,by decide⟩).scale 1 12) = p3_223.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 3 ⟨223,by decide⟩
  have he : PointBox.calc p3_223.t = p3_223 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains_e ht (by decide +kernel)

lemma row3_13_contains_e_oai (k : Fin 16) : (row3_13 k).Contains (quadraturePoint 3 (208+k.val)) := by
  fin_cases k
  · exact p3_208_contains
  · exact p3_209_contains
  · exact p3_210_contains
  · exact p3_211_contains
  · exact p3_212_contains
  · exact p3_213_contains
  · exact p3_214_contains
  · exact p3_215_contains
  · exact p3_216_contains
  · exact p3_217_contains
  · exact p3_218_contains
  · exact p3_219_contains
  · exact p3_220_contains
  · exact p3_221_contains
  · exact p3_222_contains
  · exact p3_223_contains
end SharpPlanar.IntegerGrid

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerGrid.row3_13_contains_e_oai := @OAI.SharpPlanar.IntegerGrid.row3_13_contains_e_oai
