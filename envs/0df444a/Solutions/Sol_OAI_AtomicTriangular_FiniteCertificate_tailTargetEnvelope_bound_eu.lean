-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tailTargetEnvelope_bound_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:01:48.751025+00:00
-- url     : https://prove2.me/submissions/33b42b32-3d00-4607-b9f7-3bec44a2875e

import Mathlib
import Definitions.Def_OAIQ334E020
import Definitions.Def_OAIQ334E024

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators

namespace AtomicTriangular.Interval

lemma RI.mem_invPos {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo) :
    a.invPos.Mem x⁻¹ := by
  have halo : (0:ℝ) < a.lo := by exact_mod_cast ha
  have hsx : 0 < (scale:ℝ)*x := halo.trans_le hx.1
  have hahi : (0:ℝ) < a.hi := hsx.trans_le hx.2
  have hahi' : (0:ℤ) < a.hi := by exact_mod_cast hahi
  have hl := (div_floor_bounds (scale^2) a.hi hahi').1
  have hu := (div_floor_bounds (scale^2) a.lo ha).2
  push_cast at hl hu
  have hlow : (((scale^2/a.hi:ℤ):ℝ)) ≤ (scale:ℝ)^2/((scale:ℝ)*x) := by
    exact ((le_div_iff₀ hahi).mpr hl).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hsx hx.2)
  have hupp : (scale:ℝ)^2/((scale:ℝ)*x) ≤ (((scale^2/a.lo+1:ℤ):ℝ)) := by
    exact (div_le_div_of_nonneg_left (sq_nonneg _) halo hx.1).trans
      ((div_le_iff₀ halo).mpr (by simpa only [Int.cast_add,Int.cast_one] using hu))
  have heq : (scale:ℝ)^2/((scale:ℝ)*x) = (scale:ℝ)*x⁻¹ := by
    field_simp [ne_of_gt scale_pos]
  simpa only [heq,RI.Mem,RI.invPos] using And.intro hlow hupp

noncomputable section
open scoped BigOperators

lemma RI.mem_abs {a : RI} {x : ℝ} (hx : a.Mem x) : a.abs.Mem |x| := by
  rcases hx with ⟨hl,hu⟩
  change (↑(max 0 (max a.lo (-a.hi))) : ℝ) ≤ (scale:ℝ)*|x| ∧
    (scale:ℝ)*|x| ≤ ↑(max a.hi (-a.lo))
  push_cast
  rw [← abs_of_pos scale_pos, ← abs_mul]
  constructor
  · exact max_le (abs_nonneg _) (max_le (hl.trans (le_abs_self _)) (by simpa using (neg_le_neg hu).trans (neg_le_abs _)))
  · exact (abs_le.mpr ⟨by linarith [le_max_right (a.hi:ℝ) (-(a.lo:ℝ))], hu.trans (le_max_left _ _)⟩)

lemma RI.mem_inv {a : RI} {x : ℝ} (hx : a.Mem x) (ha : 0 < a.lo ∨ a.hi < 0) :
    a.inv.Mem x⁻¹ := by
  unfold RI.inv
  split_ifs with hh
  · have hp : 0 < a.neg.lo := by simpa [RI.neg] using neg_pos.mpr hh
    simpa using RI.mem_neg (RI.mem_invPos (RI.mem_neg hx) hp)
  · exact RI.mem_invPos hx (ha.resolve_right hh)

end
end AtomicTriangular.Interval

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma jetBox3_0_calc : waveDerivativeBox 3 0 = jetBox3_0 := by decide +kernel
lemma jetBox3_0_mem : jetBox3_0.Mem (waveDerivative 3 ((0:ℤ):ℂ)) := by
  rw [← jetBox3_0_calc]
  exact waveDerivativeBox_mem 3 0
lemma DBox0_calc : jetBox3_0.re.mul ((RI.point 6).mul QBox0).inv = DBox0 := by decide +kernel
lemma DBox0_mem : DBox0.Mem (D 0) := by
  rw [← DBox0_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_0_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox0_mem
  · left; decide +kernel
lemma jetBox3_1_calc : waveDerivativeBox 3 1 = jetBox3_1 := by decide +kernel
lemma jetBox3_1_mem : jetBox3_1.Mem (waveDerivative 3 ((1:ℤ):ℂ)) := by
  rw [← jetBox3_1_calc]
  exact waveDerivativeBox_mem 3 1
lemma DBox1_calc : jetBox3_1.re.mul ((RI.point 6).mul QBox1).inv = DBox1 := by decide +kernel
lemma DBox1_mem : DBox1.Mem (D 1) := by
  rw [← DBox1_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_1_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox1_mem
  · left; decide +kernel
lemma jetBox3_3_calc : waveDerivativeBox 3 3 = jetBox3_3 := by decide +kernel
lemma jetBox3_3_mem : jetBox3_3.Mem (waveDerivative 3 ((3:ℤ):ℂ)) := by
  rw [← jetBox3_3_calc]
  exact waveDerivativeBox_mem 3 3
lemma DBox3_calc : jetBox3_3.re.mul ((RI.point 6).mul QBox3).inv = DBox3 := by decide +kernel
lemma DBox3_mem : DBox3.Mem (D 3) := by
  rw [← DBox3_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_3_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox3_mem
  · left; decide +kernel
lemma jetBox3_4_calc : waveDerivativeBox 3 4 = jetBox3_4 := by decide +kernel
lemma jetBox3_4_mem : jetBox3_4.Mem (waveDerivative 3 ((4:ℤ):ℂ)) := by
  rw [← jetBox3_4_calc]
  exact waveDerivativeBox_mem 3 4
lemma DBox4_calc : jetBox3_4.re.mul ((RI.point 6).mul QBox4).inv = DBox4 := by decide +kernel
lemma DBox4_mem : DBox4.Mem (D 4) := by
  rw [← DBox4_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_4_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox4_mem
  · left; decide +kernel
lemma jetBox3_7_calc : waveDerivativeBox 3 7 = jetBox3_7 := by decide +kernel
lemma jetBox3_7_mem : jetBox3_7.Mem (waveDerivative 3 ((7:ℤ):ℂ)) := by
  rw [← jetBox3_7_calc]
  exact waveDerivativeBox_mem 3 7
lemma DBox7_calc : jetBox3_7.re.mul ((RI.point 6).mul QBox7).inv = DBox7 := by decide +kernel
lemma DBox7_mem : DBox7.Mem (D 7) := by
  rw [← DBox7_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_7_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox7_mem
  · left; decide +kernel
lemma jetBox3_9_calc : waveDerivativeBox 3 9 = jetBox3_9 := by decide +kernel
lemma jetBox3_9_mem : jetBox3_9.Mem (waveDerivative 3 ((9:ℤ):ℂ)) := by
  rw [← jetBox3_9_calc]
  exact waveDerivativeBox_mem 3 9
lemma DBox9_calc : jetBox3_9.re.mul ((RI.point 6).mul QBox9).inv = DBox9 := by decide +kernel
lemma DBox9_mem : DBox9.Mem (D 9) := by
  rw [← DBox9_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_9_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox9_mem
  · left; decide +kernel
lemma jetBox3_12_calc : waveDerivativeBox 3 12 = jetBox3_12 := by decide +kernel
lemma jetBox3_12_mem : jetBox3_12.Mem (waveDerivative 3 ((12:ℤ):ℂ)) := by
  rw [← jetBox3_12_calc]
  exact waveDerivativeBox_mem 3 12
lemma DBox12_calc : jetBox3_12.re.mul ((RI.point 6).mul QBox12).inv = DBox12 := by decide +kernel
lemma DBox12_mem : DBox12.Mem (D 12) := by
  rw [← DBox12_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_12_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox12_mem
  · left; decide +kernel
lemma jetBox3_13_calc : waveDerivativeBox 3 13 = jetBox3_13 := by decide +kernel
lemma jetBox3_13_mem : jetBox3_13.Mem (waveDerivative 3 ((13:ℤ):ℂ)) := by
  rw [← jetBox3_13_calc]
  exact waveDerivativeBox_mem 3 13
lemma DBox13_calc : jetBox3_13.re.mul ((RI.point 6).mul QBox13).inv = DBox13 := by decide +kernel
lemma DBox13_mem : DBox13.Mem (D 13) := by
  rw [← DBox13_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_13_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox13_mem
  · left; decide +kernel
lemma jetBox3_16_calc : waveDerivativeBox 3 16 = jetBox3_16 := by decide +kernel
lemma jetBox3_16_mem : jetBox3_16.Mem (waveDerivative 3 ((16:ℤ):ℂ)) := by
  rw [← jetBox3_16_calc]
  exact waveDerivativeBox_mem 3 16
lemma DBox16_calc : jetBox3_16.re.mul ((RI.point 6).mul QBox16).inv = DBox16 := by decide +kernel
lemma DBox16_mem : DBox16.Mem (D 16) := by
  rw [← DBox16_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_16_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox16_mem
  · left; decide +kernel
lemma jetBox3_19_calc : waveDerivativeBox 3 19 = jetBox3_19 := by decide +kernel
lemma jetBox3_19_mem : jetBox3_19.Mem (waveDerivative 3 ((19:ℤ):ℂ)) := by
  rw [← jetBox3_19_calc]
  exact waveDerivativeBox_mem 3 19
lemma DBox19_calc : jetBox3_19.re.mul ((RI.point 6).mul QBox19).inv = DBox19 := by decide +kernel
lemma DBox19_mem : DBox19.Mem (D 19) := by
  rw [← DBox19_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_19_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox19_mem
  · left; decide +kernel
lemma jetBox3_21_calc : waveDerivativeBox 3 21 = jetBox3_21 := by decide +kernel
lemma jetBox3_21_mem : jetBox3_21.Mem (waveDerivative 3 ((21:ℤ):ℂ)) := by
  rw [← jetBox3_21_calc]
  exact waveDerivativeBox_mem 3 21
lemma DBox21_calc : jetBox3_21.re.mul ((RI.point 6).mul QBox21).inv = DBox21 := by decide +kernel
lemma DBox21_mem : DBox21.Mem (D 21) := by
  rw [← DBox21_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_21_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox21_mem
  · left; decide +kernel
lemma jetBox3_25_calc : waveDerivativeBox 3 25 = jetBox3_25 := by decide +kernel
lemma jetBox3_25_mem : jetBox3_25.Mem (waveDerivative 3 ((25:ℤ):ℂ)) := by
  rw [← jetBox3_25_calc]
  exact waveDerivativeBox_mem 3 25
lemma DBox25_calc : jetBox3_25.re.mul ((RI.point 6).mul QBox25).inv = DBox25 := by decide +kernel
lemma DBox25_mem : DBox25.Mem (D 25) := by
  rw [← DBox25_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_25_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox25_mem
  · left; decide +kernel
lemma jetBox3_27_calc : waveDerivativeBox 3 27 = jetBox3_27 := by decide +kernel
lemma jetBox3_27_mem : jetBox3_27.Mem (waveDerivative 3 ((27:ℤ):ℂ)) := by
  rw [← jetBox3_27_calc]
  exact waveDerivativeBox_mem 3 27
lemma DBox27_calc : jetBox3_27.re.mul ((RI.point 6).mul QBox27).inv = DBox27 := by decide +kernel
lemma DBox27_mem : DBox27.Mem (D 27) := by
  rw [← DBox27_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_27_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox27_mem
  · left; decide +kernel
lemma jetBox3_28_calc : waveDerivativeBox 3 28 = jetBox3_28 := by decide +kernel
lemma jetBox3_28_mem : jetBox3_28.Mem (waveDerivative 3 ((28:ℤ):ℂ)) := by
  rw [← jetBox3_28_calc]
  exact waveDerivativeBox_mem 3 28
lemma DBox28_calc : jetBox3_28.re.mul ((RI.point 6).mul QBox28).inv = DBox28 := by decide +kernel
lemma DBox28_mem : DBox28.Mem (D 28) := by
  rw [← DBox28_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_28_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox28_mem
  · left; decide +kernel
lemma jetBox3_31_calc : waveDerivativeBox 3 31 = jetBox3_31 := by decide +kernel
lemma jetBox3_31_mem : jetBox3_31.Mem (waveDerivative 3 ((31:ℤ):ℂ)) := by
  rw [← jetBox3_31_calc]
  exact waveDerivativeBox_mem 3 31
lemma DBox31_calc : jetBox3_31.re.mul ((RI.point 6).mul QBox31).inv = DBox31 := by decide +kernel
lemma DBox31_mem : DBox31.Mem (D 31) := by
  rw [← DBox31_calc]
  unfold D
  rw [div_eq_mul_inv]
  apply RI.mem_mul jetBox3_31_mem.1
  apply RI.mem_inv
  · simpa only [Int.cast_ofNat] using RI.mem_mul (RI.mem_point 6) QBox31_mem
  · left; decide +kernel
end AtomicTriangular.FiniteCertificate

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri0_mem : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeSumsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_TargetInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma targetZBox_mem : targetZBox.Mem Z := by
  simpa [Z,targetZBox] using RI.mem_divNat (RI.mem_point 391) (by norm_num : 0<1000)
lemma targetRateBox_mem (q : Fin 2) : (targetRateBox q).Mem (Real.pi*(damping q-h)) := by
  fin_cases q
  · simpa [targetRateBox,damping] using ri0_mem
  · convert RI.mem_mul piBox_mem (RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [targetRateBox,damping,H,h])
lemma targetExpInput_mem (q : Fin 2) (n : ℤ) :
    (targetExpInput q n).Mem (Real.pi*(damping q-h)*n+(1-n)/Z) := by
  apply RI.mem_add (RI.mem_mul (targetRateBox_mem q) (RI.mem_point n))
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_point (1-n))
    (RI.mem_invPos targetZBox_mem (by decide +kernel))
lemma targetEnvBox_mem (q : Fin 2) (n : ℤ) {qb db eb : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (he : eb.Mem (Real.exp (Real.pi*(damping q-h)*n+(1-n)/Z))) (hp : 0<qb.lo) :
    (targetEnvBox q qb db eb).Mem (targetEnvelope (damping q) n) := by
  unfold targetEnvelope
  rw [div_eq_mul_inv]
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos hq hp))
    (RI.mem_add (RI.mem_add ri1_mem targetZBox_mem)
      (RI.mem_mul targetZBox_mem (RI.mem_abs (RI.mem_sub (targetRateBox_mem q) hd))))) he

lemma targetExpt36_calc : (CI.ofReal (targetExpInput 0 36)).exp.re=targetExpt36 := by decide +kernel
lemma targetExpt36_mem : targetExpt36.Mem (Real.exp (Real.pi*(damping 0-h)*(36:ℤ)+(1-(36:ℤ))/Z)) := by
  rw [← targetExpt36_calc]
  exact ri_exp_mem (targetExpInput_mem 0 36) (by decide +kernel)
lemma targetEnvt36_calc : targetEnvBox 0 QBox0 DBox0 targetExpt36=targetEnvt36 := by decide +kernel
lemma targetEnvt36_mem : targetEnvt36.Mem (targetEnvelope (damping 0) 36) := by
  rw [← targetEnvt36_calc]
  apply targetEnvBox_mem 0 36 _ _ targetExpt36_mem (by decide +kernel)
  · rw [Q_emod 36]; norm_num; exact QBox0_mem
  · rw [D_emod 36]; norm_num; exact DBox0_mem
lemma targetExpt37_calc : (CI.ofReal (targetExpInput 0 37)).exp.re=targetExpt37 := by decide +kernel
lemma targetExpt37_mem : targetExpt37.Mem (Real.exp (Real.pi*(damping 0-h)*(37:ℤ)+(1-(37:ℤ))/Z)) := by
  rw [← targetExpt37_calc]
  exact ri_exp_mem (targetExpInput_mem 0 37) (by decide +kernel)
lemma targetEnvt37_calc : targetEnvBox 0 QBox1 DBox1 targetExpt37=targetEnvt37 := by decide +kernel
lemma targetEnvt37_mem : targetEnvt37.Mem (targetEnvelope (damping 0) 37) := by
  rw [← targetEnvt37_calc]
  apply targetEnvBox_mem 0 37 _ _ targetExpt37_mem (by decide +kernel)
  · rw [Q_emod 37]; norm_num; exact QBox1_mem
  · rw [D_emod 37]; norm_num; exact DBox1_mem
lemma targetExpt39_calc : (CI.ofReal (targetExpInput 0 39)).exp.re=targetExpt39 := by decide +kernel
lemma targetExpt39_mem : targetExpt39.Mem (Real.exp (Real.pi*(damping 0-h)*(39:ℤ)+(1-(39:ℤ))/Z)) := by
  rw [← targetExpt39_calc]
  exact ri_exp_mem (targetExpInput_mem 0 39) (by decide +kernel)
lemma targetEnvt39_calc : targetEnvBox 0 QBox3 DBox3 targetExpt39=targetEnvt39 := by decide +kernel
lemma targetEnvt39_mem : targetEnvt39.Mem (targetEnvelope (damping 0) 39) := by
  rw [← targetEnvt39_calc]
  apply targetEnvBox_mem 0 39 _ _ targetExpt39_mem (by decide +kernel)
  · rw [Q_emod 39]; norm_num; exact QBox3_mem
  · rw [D_emod 39]; norm_num; exact DBox3_mem
lemma targetExpt40_calc : (CI.ofReal (targetExpInput 0 40)).exp.re=targetExpt40 := by decide +kernel
lemma targetExpt40_mem : targetExpt40.Mem (Real.exp (Real.pi*(damping 0-h)*(40:ℤ)+(1-(40:ℤ))/Z)) := by
  rw [← targetExpt40_calc]
  exact ri_exp_mem (targetExpInput_mem 0 40) (by decide +kernel)
lemma targetEnvt40_calc : targetEnvBox 0 QBox4 DBox4 targetExpt40=targetEnvt40 := by decide +kernel
lemma targetEnvt40_mem : targetEnvt40.Mem (targetEnvelope (damping 0) 40) := by
  rw [← targetEnvt40_calc]
  apply targetEnvBox_mem 0 40 _ _ targetExpt40_mem (by decide +kernel)
  · rw [Q_emod 40]; norm_num; exact QBox4_mem
  · rw [D_emod 40]; norm_num; exact DBox4_mem
lemma targetExpt43_calc : (CI.ofReal (targetExpInput 0 43)).exp.re=targetExpt43 := by decide +kernel
lemma targetExpt43_mem : targetExpt43.Mem (Real.exp (Real.pi*(damping 0-h)*(43:ℤ)+(1-(43:ℤ))/Z)) := by
  rw [← targetExpt43_calc]
  exact ri_exp_mem (targetExpInput_mem 0 43) (by decide +kernel)
lemma targetEnvt43_calc : targetEnvBox 0 QBox7 DBox7 targetExpt43=targetEnvt43 := by decide +kernel
lemma targetEnvt43_mem : targetEnvt43.Mem (targetEnvelope (damping 0) 43) := by
  rw [← targetEnvt43_calc]
  apply targetEnvBox_mem 0 43 _ _ targetExpt43_mem (by decide +kernel)
  · rw [Q_emod 43]; norm_num; exact QBox7_mem
  · rw [D_emod 43]; norm_num; exact DBox7_mem
lemma targetExpt45_calc : (CI.ofReal (targetExpInput 0 45)).exp.re=targetExpt45 := by decide +kernel
lemma targetExpt45_mem : targetExpt45.Mem (Real.exp (Real.pi*(damping 0-h)*(45:ℤ)+(1-(45:ℤ))/Z)) := by
  rw [← targetExpt45_calc]
  exact ri_exp_mem (targetExpInput_mem 0 45) (by decide +kernel)
lemma targetEnvt45_calc : targetEnvBox 0 QBox9 DBox9 targetExpt45=targetEnvt45 := by decide +kernel
lemma targetEnvt45_mem : targetEnvt45.Mem (targetEnvelope (damping 0) 45) := by
  rw [← targetEnvt45_calc]
  apply targetEnvBox_mem 0 45 _ _ targetExpt45_mem (by decide +kernel)
  · rw [Q_emod 45]; norm_num; exact QBox9_mem
  · rw [D_emod 45]; norm_num; exact DBox9_mem
lemma targetExpt48_calc : (CI.ofReal (targetExpInput 0 48)).exp.re=targetExpt48 := by decide +kernel
lemma targetExpt48_mem : targetExpt48.Mem (Real.exp (Real.pi*(damping 0-h)*(48:ℤ)+(1-(48:ℤ))/Z)) := by
  rw [← targetExpt48_calc]
  exact ri_exp_mem (targetExpInput_mem 0 48) (by decide +kernel)
lemma targetEnvt48_calc : targetEnvBox 0 QBox12 DBox12 targetExpt48=targetEnvt48 := by decide +kernel
lemma targetEnvt48_mem : targetEnvt48.Mem (targetEnvelope (damping 0) 48) := by
  rw [← targetEnvt48_calc]
  apply targetEnvBox_mem 0 48 _ _ targetExpt48_mem (by decide +kernel)
  · rw [Q_emod 48]; norm_num; exact QBox12_mem
  · rw [D_emod 48]; norm_num; exact DBox12_mem
lemma targetExpt49_calc : (CI.ofReal (targetExpInput 0 49)).exp.re=targetExpt49 := by decide +kernel
lemma targetExpt49_mem : targetExpt49.Mem (Real.exp (Real.pi*(damping 0-h)*(49:ℤ)+(1-(49:ℤ))/Z)) := by
  rw [← targetExpt49_calc]
  exact ri_exp_mem (targetExpInput_mem 0 49) (by decide +kernel)
lemma targetEnvt49_calc : targetEnvBox 0 QBox13 DBox13 targetExpt49=targetEnvt49 := by decide +kernel
lemma targetEnvt49_mem : targetEnvt49.Mem (targetEnvelope (damping 0) 49) := by
  rw [← targetEnvt49_calc]
  apply targetEnvBox_mem 0 49 _ _ targetExpt49_mem (by decide +kernel)
  · rw [Q_emod 49]; norm_num; exact QBox13_mem
  · rw [D_emod 49]; norm_num; exact DBox13_mem
lemma targetExpt52_calc : (CI.ofReal (targetExpInput 0 52)).exp.re=targetExpt52 := by decide +kernel
lemma targetExpt52_mem : targetExpt52.Mem (Real.exp (Real.pi*(damping 0-h)*(52:ℤ)+(1-(52:ℤ))/Z)) := by
  rw [← targetExpt52_calc]
  exact ri_exp_mem (targetExpInput_mem 0 52) (by decide +kernel)
lemma targetEnvt52_calc : targetEnvBox 0 QBox16 DBox16 targetExpt52=targetEnvt52 := by decide +kernel
lemma targetEnvt52_mem : targetEnvt52.Mem (targetEnvelope (damping 0) 52) := by
  rw [← targetEnvt52_calc]
  apply targetEnvBox_mem 0 52 _ _ targetExpt52_mem (by decide +kernel)
  · rw [Q_emod 52]; norm_num; exact QBox16_mem
  · rw [D_emod 52]; norm_num; exact DBox16_mem
lemma targetExpt55_calc : (CI.ofReal (targetExpInput 0 55)).exp.re=targetExpt55 := by decide +kernel
lemma targetExpt55_mem : targetExpt55.Mem (Real.exp (Real.pi*(damping 0-h)*(55:ℤ)+(1-(55:ℤ))/Z)) := by
  rw [← targetExpt55_calc]
  exact ri_exp_mem (targetExpInput_mem 0 55) (by decide +kernel)
lemma targetEnvt55_calc : targetEnvBox 0 QBox19 DBox19 targetExpt55=targetEnvt55 := by decide +kernel
lemma targetEnvt55_mem : targetEnvt55.Mem (targetEnvelope (damping 0) 55) := by
  rw [← targetEnvt55_calc]
  apply targetEnvBox_mem 0 55 _ _ targetExpt55_mem (by decide +kernel)
  · rw [Q_emod 55]; norm_num; exact QBox19_mem
  · rw [D_emod 55]; norm_num; exact DBox19_mem
lemma targetExpt57_calc : (CI.ofReal (targetExpInput 0 57)).exp.re=targetExpt57 := by decide +kernel
lemma targetExpt57_mem : targetExpt57.Mem (Real.exp (Real.pi*(damping 0-h)*(57:ℤ)+(1-(57:ℤ))/Z)) := by
  rw [← targetExpt57_calc]
  exact ri_exp_mem (targetExpInput_mem 0 57) (by decide +kernel)
lemma targetEnvt57_calc : targetEnvBox 0 QBox21 DBox21 targetExpt57=targetEnvt57 := by decide +kernel
lemma targetEnvt57_mem : targetEnvt57.Mem (targetEnvelope (damping 0) 57) := by
  rw [← targetEnvt57_calc]
  apply targetEnvBox_mem 0 57 _ _ targetExpt57_mem (by decide +kernel)
  · rw [Q_emod 57]; norm_num; exact QBox21_mem
  · rw [D_emod 57]; norm_num; exact DBox21_mem
lemma targetExpt25_calc : (CI.ofReal (targetExpInput 0 25)).exp.re=targetExpt25 := by decide +kernel
lemma targetExpt25_mem : targetExpt25.Mem (Real.exp (Real.pi*(damping 0-h)*(25:ℤ)+(1-(25:ℤ))/Z)) := by
  rw [← targetExpt25_calc]
  exact ri_exp_mem (targetExpInput_mem 0 25) (by decide +kernel)
lemma targetEnvt25_calc : targetEnvBox 0 QBox25 DBox25 targetExpt25=targetEnvt25 := by decide +kernel
lemma targetEnvt25_mem : targetEnvt25.Mem (targetEnvelope (damping 0) 25) := by
  rw [← targetEnvt25_calc]
  apply targetEnvBox_mem 0 25 _ _ targetExpt25_mem (by decide +kernel)
  · exact QBox25_mem
  · exact DBox25_mem
lemma targetExpt27_calc : (CI.ofReal (targetExpInput 0 27)).exp.re=targetExpt27 := by decide +kernel
lemma targetExpt27_mem : targetExpt27.Mem (Real.exp (Real.pi*(damping 0-h)*(27:ℤ)+(1-(27:ℤ))/Z)) := by
  rw [← targetExpt27_calc]
  exact ri_exp_mem (targetExpInput_mem 0 27) (by decide +kernel)
lemma targetEnvt27_calc : targetEnvBox 0 QBox27 DBox27 targetExpt27=targetEnvt27 := by decide +kernel
lemma targetEnvt27_mem : targetEnvt27.Mem (targetEnvelope (damping 0) 27) := by
  rw [← targetEnvt27_calc]
  apply targetEnvBox_mem 0 27 _ _ targetExpt27_mem (by decide +kernel)
  · exact QBox27_mem
  · exact DBox27_mem
lemma targetExpt28_calc : (CI.ofReal (targetExpInput 0 28)).exp.re=targetExpt28 := by decide +kernel
lemma targetExpt28_mem : targetExpt28.Mem (Real.exp (Real.pi*(damping 0-h)*(28:ℤ)+(1-(28:ℤ))/Z)) := by
  rw [← targetExpt28_calc]
  exact ri_exp_mem (targetExpInput_mem 0 28) (by decide +kernel)
lemma targetEnvt28_calc : targetEnvBox 0 QBox28 DBox28 targetExpt28=targetEnvt28 := by decide +kernel
lemma targetEnvt28_mem : targetEnvt28.Mem (targetEnvelope (damping 0) 28) := by
  rw [← targetEnvt28_calc]
  apply targetEnvBox_mem 0 28 _ _ targetExpt28_mem (by decide +kernel)
  · exact QBox28_mem
  · exact DBox28_mem
lemma targetExpt31_calc : (CI.ofReal (targetExpInput 0 31)).exp.re=targetExpt31 := by decide +kernel
lemma targetExpt31_mem : targetExpt31.Mem (Real.exp (Real.pi*(damping 0-h)*(31:ℤ)+(1-(31:ℤ))/Z)) := by
  rw [← targetExpt31_calc]
  exact ri_exp_mem (targetExpInput_mem 0 31) (by decide +kernel)
lemma targetEnvt31_calc : targetEnvBox 0 QBox31 DBox31 targetExpt31=targetEnvt31 := by decide +kernel
lemma targetEnvt31_mem : targetEnvt31.Mem (targetEnvelope (damping 0) 31) := by
  rw [← targetEnvt31_calc]
  apply targetEnvBox_mem 0 31 _ _ targetExpt31_mem (by decide +kernel)
  · exact QBox31_mem
  · exact DBox31_mem
lemma targetEnvTablet_mem (i : Fin 15) : (targetEnvTablet i).Mem (targetEnvelope (damping 0) (tailBase i)) := by
  fin_cases i
  · exact targetEnvt36_mem
  · exact targetEnvt37_mem
  · exact targetEnvt39_mem
  · exact targetEnvt40_mem
  · exact targetEnvt43_mem
  · exact targetEnvt45_mem
  · exact targetEnvt48_mem
  · exact targetEnvt49_mem
  · exact targetEnvt52_mem
  · exact targetEnvt55_mem
  · exact targetEnvt57_mem
  · exact targetEnvt25_mem
  · exact targetEnvt27_mem
  · exact targetEnvt28_mem
  · exact targetEnvt31_mem
lemma targetRatioBox_calc : (CI.ofReal ((RI.point (-36)).mul targetZBox.invPos)).exp.re=targetRatioBox := by decide +kernel
lemma targetRatioBox_mem : targetRatioBox.Mem (Real.exp (-36/Z)) := by
  rw [←targetRatioBox_calc]
  apply ri_exp_mem
  · rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-36)) (RI.mem_invPos targetZBox_mem (by decide +kernel))
  · decide +kernel
lemma tailTargetBox_calc : (RI.sum targetEnvTablet).mul (((RI.point 1).sub targetRatioBox).invPos)=tailTargetBox := by decide +kernel
lemma tailTargetEnvelope_bound_eu_oai : tailTargetEnvelope < (92/10^30:ℝ) := by
  have hh := RI.mem_mul (RI.mem_sum targetEnvTablet_mem)
    (RI.mem_invPos (RI.mem_sub ri1_mem targetRatioBox_mem) (by decide +kernel))
  rw [tailTargetBox_calc] at hh
  have hb := ri_mem_lt hh 92 (10^30) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tailTargetEnvelope_bound_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tailTargetEnvelope_bound_eu_oai
