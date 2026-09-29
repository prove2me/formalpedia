-- Prove2me | solution 1 for ModularCurve.exists_hauptmodulFive_of_kernelQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f56e82c9-9ffc-550a-a335-1b950fdd5d75

import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic

namespace ModularCurve
namespace ProducerFivePort

theorem fiveKernel_clearedMembership (A B p q : ℚ)
    (hg3 : 2*A*p - 4*B - p^3 + 6*p*q = 0)
    (hg4 : A^2 - 2*A*q + 4*B*p - p^2*q + 5*q^2 = 0) :
    ((8*B - 5*p^3 + 28*p*q)^2
        + 10*(8*B - 5*p^3 + 28*p*q)*(p^3 - 4*p*q)
        + 5*(p^3 - 4*p*q)^2)^3 * (-16*(4*A^3 + 27*B^2))
      = (-48*A)^3 * (8*B - 5*p^3 + 28*p*q) * (p^3 - 4*p*q)^5 := by
  linear_combination
    (20480*p^19*q - 20480*A^2*p^17 + 81920*A*p^17*q - 81920*B*p^18 - 872448*p^17*q^2 +
      933888*A^2*p^15*q - 163840*A*B*p^16 - 3039232*A*p^15*q^2 + 2310144*B*p^16*q +
      14974976*p^15*q^3 + 442368*A^2*B*p^14 - 16220160*A^2*p^13*q^2 + 1933312*A*B*p^14*q +
      43204608*A*p^13*q^3 - 375808*B^2*p^15 - 25640960*B*p^14*q^2 - 136101888*p^13*q^4 -
      13762560*A^2*B*p^12*q + 136314880*A^2*p^11*q^3 - 96256*A*B^2*p^13 +
      5570560*A*B*p^12*q^2 - 307429376*A*p^11*q^4 + 5752832*B^2*p^13*q +
      136445952*B*p^12*q^3 + 712376320*p^11*q^5 - 2457600*A^2*B^2*p^11 +
      149422080*A^2*B*p^10*q^2 - 589824000*A^2*p^9*q^4 + 4186112*A*B^2*p^11*q -
      178454528*A*B*p^10*q^3 + 1165885440*A*p^9*q^5 - 479232*B^3*p^12 -
      28401664*B^2*p^11*q^2 - 310575104*B*p^10*q^4 - 2155479040*p^9*q^6 +
      39321600*A^2*B^2*p^9*q - 723517440*A^2*B*p^8*q^3 + 1258291200*A^2*p^7*q^5 -
      573440*A*B^3*p^10 - 35258368*A*B^2*p^9*q^2 + 973602816*A*B*p^8*q^4 -
      2246574080*A*p^7*q^6 + 11730944*B^3*p^10*q + 14811136*B^2*p^9*q^3 - 47972352*B*p^8*q^5 +
      3499622400*p^7*q^7 - 188743680*A^2*B^2*p^7*q^2 + 1572864000*A^2*B*p^6*q^4 -
      1048576000*A^2*p^5*q^6 + 20643840*A*B^3*p^8*q + 44826624*A*B^2*p^7*q^3 -
      2132803584*A*B*p^6*q^5 + 1730150400*A*p^5*q^7 + 360448*B^4*p^9 - 94437376*B^3*p^8*q^2 +
      386138112*B^2*p^7*q^4 + 1347420160*B*p^6*q^6 - 2359296000*p^5*q^8 +
      31457280*A^2*B^3*p^6*q + 251658240*A^2*B^2*p^5*q^3 - 1258291200*A^2*B*p^4*q^5 +
      3014656*A*B^4*p^7 - 218890240*A*B^3*p^6*q^2 + 346030080*A*B^2*p^5*q^4 +
      1677721600*A*B*p^4*q^6 + 12386304*B^4*p^7*q + 416022528*B^3*p^6*q^3 -
      1576009728*B^2*p^5*q^5 - 1572864000*B*p^4*q^7 + 7864320*A^2*B^4*p^5 -
      251658240*A^2*B^3*p^4*q^2 - 43384832*A*B^4*p^5*q + 854589440*A*B^3*p^4*q^3 -
      723517440*A*B^2*p^3*q^5 + 5898240*B^5*p^6 - 123600896*B^4*p^5*q^2 -
      1211105280*B^3*p^4*q^4 + 1939865600*B^2*p^3*q^6 - 62914560*A^2*B^4*p^3*q +
      335544320*A^2*B^3*p^2*q^3 - 262144*A*B^5*p^4 + 163053568*A*B^4*p^3*q^2 -
      964689920*A*B^3*p^2*q^4 - 60817408*B^5*p^4*q + 236453888*B^4*p^3*q^3 +
      1363148800*B^3*p^2*q^5 - 13631488*A*B^5*p^2*q - 56623104*A*B^4*p*q^3 - 1835008*B^6*p^3 +
      140509184*B^5*p^2*q^2 - 304087040*B^4*p*q^4 - 50331648*A^2*B^5*q - 2621440*A*B^6*p +
      96468992*A*B^5*q^2 - 22544384*B^6*p*q - 293601280*B^5*q^3 + 28311552*B^7) * hg3 +
    (-20480*p^20 + 892928*p^18*q + 688128*B*p^17 - 15745024*p^16*q^2 - 16547840*B*p^15*q +
      147226624*p^14*q^3 - 495616*B^2*p^14 + 155975680*B*p^13*q^2 - 792854528*p^12*q^4 -
      9355264*B^2*p^12*q - 717881344*B*p^11*q^3 + 2465464320*p^10*q^5 - 8683520*B^3*p^11 +
      243531776*B^2*p^10*q^2 + 1607467008*B*p^9*q^4 - 4105175040*p^8*q^6 +
      147456000*B^3*p^9*q - 1599602688*B^2*p^8*q^3 - 1396703232*B*p^7*q^5 +
      2831155200*p^6*q^7 + 1835008*B^4*p^8 - 757596160*B^3*p^7*q^2 + 4089446400*B^2*p^6*q^4 +
      102498304*B^4*p^6*q + 1142947840*B^3*p^5*q^3 - 3586129920*B^2*p^4*q^5 +
      31981568*B^5*p^5 - 955252736*B^4*p^4*q^2 - 83886080*B^3*p^3*q^4 - 274726912*B^5*p^3*q +
      1455423488*B^4*p^2*q^3 + 5242880*B^6*p^2 + 109051904*B^5*p*q^2 - 16777216*A*B^6 -
      234881024*B^6*q) * hg4

theorem hauptmodulFive_of_clearedMembership {N D W C u : ℚ} (hD : D ≠ 0) (hN : N = u * D)
    (key : (N^2 + 10*N*D + 5*D^2)^3 * W = C * N * D^5) :
    (u^2 + 10*u + 5)^3 * W = C * u := by
  apply mul_left_cancel₀ (pow_ne_zero 6 hD)
  calc D^6 * ((u^2 + 10*u + 5)^3 * W)
      = ((u * D)^2 + 10*(u * D)*D + 5*D^2)^3 * W := by ring
    _ = (N^2 + 10*N*D + 5*D^2)^3 * W := by rw [← hN]
    _ = C * N * D^5 := key
    _ = C * (u * D) * D^5 := by rw [hN]
    _ = D^6 * (C * u) := by ring

theorem eq_zero_and_eq_zero_of_sq_add_sq_eq_zero {a b : ℚ} (h : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  by_contra hcon
  rw [not_and_or] at hcon
  have hpos : (0 : ℚ) < a ^ 2 + b ^ 2 := by
    rcases hcon with ha | hb
    · exact add_pos_of_pos_of_nonneg
        (lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))) (sq_nonneg b)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg a)
        (lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb)))
  exact absurd h (ne_of_gt hpos)

theorem p_ne_zero_of_duplicationClosed {A B p q : ℚ} (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hg3 : 2 * A * p - 4 * B - p ^ 3 + 6 * p * q = 0)
    (hg4 : A ^ 2 - 2 * A * q + 4 * B * p - p ^ 2 * q + 5 * q ^ 2 = 0) :
    p ≠ 0 := by
  intro hp0
  apply hΔ
  subst hp0
  have hB : B = 0 := by linear_combination (-1 / 4 : ℚ) * hg3
  subst hB
  have hsq : (A - q) ^ 2 + (2 * q) ^ 2 = 0 := by linear_combination hg4
  obtain ⟨hAq, hq⟩ := eq_zero_and_eq_zero_of_sq_add_sq_eq_zero hsq
  have hq0 : q = 0 := by linear_combination (1 / 2 : ℚ) * hq
  have hA0 : A = 0 := by linear_combination hAq + hq0
  rw [hA0]
  ring

theorem exists_hauptmodulFive_of_kernelQuadratic (A B p q : ℚ)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hsep : p ^ 2 - 4 * q ≠ 0)
    (hg3 : 2 * A * p - 4 * B - p ^ 3 + 6 * p * q = 0)
    (hg4 : A ^ 2 - 2 * A * q + 4 * B * p - p ^ 2 * q + 5 * q ^ 2 = 0) :
    ∃ v : ℚ, v ≠ 0 ∧
      (v ^ 2 + 10 * v + 5) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 * v := by
  have hp : p ≠ 0 := p_ne_zero_of_duplicationClosed hΔ hg3 hg4

  have hD : p^3 - 4*p*q ≠ 0 := by
    have hfac : p^3 - 4*p*q = p * (p^2 - 4*q) := by ring
    rw [hfac]
    exact mul_ne_zero hp hsep

  have mem :
      (((8*B - 5*p^3 + 28*p*q) / (p^3 - 4*p*q))^2
          + 10*((8*B - 5*p^3 + 28*p*q) / (p^3 - 4*p*q)) + 5)^3 * (-16*(4*A^3 + 27*B^2))
        = (-48*A)^3 * ((8*B - 5*p^3 + 28*p*q) / (p^3 - 4*p*q)) :=
    hauptmodulFive_of_clearedMembership hD
      (div_mul_cancel₀ (8*B - 5*p^3 + 28*p*q) hD).symm
      (fiveKernel_clearedMembership A B p q hg3 hg4)

  refine ⟨(8*B - 5*p^3 + 28*p*q) / (p^3 - 4*p*q), ?_, mem⟩
  intro hu0
  apply hΔ
  have h0 : ((0:ℚ)^2 + 10*0 + 5)^3 * (-16*(4*A^3 + 27*B^2)) = (-48*A)^3 * 0 := by
    rw [← hu0]; exact mem
  linear_combination (-1/2000 : ℚ) * h0

end ModularCurve.ProducerFivePort

theorem solution (A B p q : ℚ) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hsep : p ^ 2 - 4 * q ≠ 0)
    (hg3 : 2 * A * p - 4 * B - p ^ 3 + 6 * p * q = 0)
    (hg4 : A ^ 2 - 2 * A * q + 4 * B * p - p ^ 2 * q + 5 * q ^ 2 = 0) :
    ∃ v : ℚ, v ≠ 0 ∧ (v ^ 2 + 10 * v + 5) ^ 3 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = (-48 * A) ^ 3 * v :=
  ModularCurve.ProducerFivePort.exists_hauptmodulFive_of_kernelQuadratic A B p q hΔ hsep hg3 hg4

end S_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic
end P2MW
export P2MW.S_ModularCurve_exists_hauptmodulFive_of_kernelQuadratic (solution)
