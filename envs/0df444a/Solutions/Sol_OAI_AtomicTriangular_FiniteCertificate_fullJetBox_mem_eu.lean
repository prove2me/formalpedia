-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:03:07.292952+00:00
-- url     : https://prove2.me/submissions/93030159-c565-422f-a61b-fb5ea7a82e1b

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E009
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExpTable_mem_eu

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

lemma RI.mem_pow {a : RI} {x : ℝ} (hx : a.Mem x) (n : ℕ) : (a.pow n).Mem (x^n) := by
  induction n with
  | zero => simpa [RI.pow] using RI.mem_point 1
  | succ n ih => simpa [RI.pow,pow_succ] using RI.mem_mul ih hx

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
namespace AtomicTriangular.Constants

lemma bStar_bracket : bStar < Real.sqrt 3 / 2 ∧ Real.sqrt 3 / 2 < bStar + eps := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3:ℝ)
  have hp : 0 < bStar := by norm_num [bStar]
  have he : 0 < eps := by norm_num [eps]
  have h₁ : bStar^2 < (3:ℝ)/4 := by norm_num [bStar]
  have h₂ : (3:ℝ)/4 < (bStar+eps)^2 := by norm_num [bStar, eps]
  constructor <;> nlinarith

end AtomicTriangular.Constants

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
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
end AtomicTriangular.FiniteCertificate

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

lemma bBox_mem : bBox.Mem b := by
  obtain ⟨hl,hu⟩ := Constants.bStar_bracket
  constructor <;> dsimp [RI.Mem, bBox]
  · have hr : (bBox.lo:ℝ)/(scale:ℝ) ≤ Constants.bStar := by norm_num [bBox,scale,Constants.bStar]
    simpa only [b, mul_comm, bBox] using (div_le_iff₀ scale_pos).mp (hr.trans hl.le)
  · have hr : Constants.bStar+Constants.eps ≤ (bBox.hi:ℝ)/(scale:ℝ) := by
      norm_num [bBox,scale,Constants.bStar,Constants.eps]
    simpa only [b,mul_comm,bBox] using (le_div_iff₀ scale_pos).mp (hu.le.trans hr)

lemma dampingBox_mem (q : Fin 2) : (dampingBox q).Mem (damping q) := by
  unfold dampingBox damping h H
  split_ifs
  · simpa using RI.mem_divNat (RI.mem_point 17) (by norm_num : 0<(50:ℕ))
  · simpa using RI.mem_divNat (RI.mem_point 27) (by norm_num : 0<(50:ℕ))
lemma realFrequencyBox_mem (j : Fin 31) : (realFrequencyBox j).Mem (frequency j) := by
  have hh := RI.mem_divNat (RI.mem_point ((j.val:ℤ)-15)) (by norm_num : 0<(18:ℕ))
  simpa only [realFrequencyBox, frequency, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_ofNat] using hh

lemma denBox_mem (q : Fin 2) (j : Fin 31) :
    (denBox q j).Mem (waveDen (damping q) (frequency j)) := by
  exact RI.mem_add (RI.mem_pow (dampingBox_mem q) 2) (RI.mem_pow (realFrequencyBox_mem j) 2)
lemma denBox_pos (q : Fin 2) (j : Fin 31) : 0 < (denBox q j).lo := by
  revert q j
  decide +kernel
lemma bdenBox_pos (q : Fin 2) (j : Fin 31) : 0 < (bBox.mul (denBox q j)).lo := by
  revert q j
  decide +kernel

lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

lemma lambdaBox_mem (q : Fin 2) (j : Fin 31) :
    (lambdaBox q j).Mem (lambda (damping q) (frequency j)) := by
  unfold lambda
  rw [div_eq_mul_inv,← Complex.ofReal_inv]
  exact CI.mem_mul (CI.mem_add (CI.mem_ofReal (dampingBox_mem q))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal (realFrequencyBox_mem j))))
    (CI.mem_ofReal (RI.mem_invPos (RI.mem_mul bBox_mem (denBox_mem q j)) (bdenBox_pos q j)))

lemma zetaBox_mem (q v : Fin 2) (j : Fin 31) :
    (zetaBox q v j).Mem (zeta (damping q) (damping v) (frequency j)) := by
  have hh := CI.mem_add (CI.mem_ofReal (RI.mem_neg
    (RI.mem_mul (realFrequencyBox_mem j) (xwaveBox_mem q j))))
    (CI.mem_mul CI.mem_imag (CI.mem_ofReal
      (RI.mem_sub (RI.mem_mul (dampingBox_mem q) (xwaveBox_mem q j)) (dampingBox_mem v))))
  simpa only [zetaBox,zeta,Complex.ofReal_neg,Complex.ofReal_mul,neg_mul] using hh

lemma wavePhaseBox_mem (q v : Fin 2) (j : Fin 31) :
    (wavePhaseBox q v j).Mem (I*Real.pi*zeta (damping q) (damping v) (frequency j)) :=
  CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (zetaBox_mem q v j)
end AtomicTriangular.FiniteCertificate
end
end
end
end
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
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveExpData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma lambdaTable0_calc (j : Fin 31) : lambdaBox 0 j = lambdaTable0 j := by
  revert j
  decide +kernel
lemma lambdaTable0_mem (j : Fin 31) : (lambdaTable0 j).Mem (lambda (damping 0) (frequency j)) := by
  rw [← lambdaTable0_calc]
  exact lambdaBox_mem 0 j
lemma phaseHTable0_calc (j : Fin 31) : wavePhaseBox 0 1 j = phaseHTable0 j := by
  revert j
  decide +kernel
lemma phaseHTable0_mem (j : Fin 31) : (phaseHTable0 j).Mem (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)) := by
  rw [← phaseHTable0_calc]
  exact wavePhaseBox_mem 0 1 j
lemma lambdaTable1_calc (j : Fin 31) : lambdaBox 1 j = lambdaTable1 j := by
  revert j
  decide +kernel
lemma lambdaTable1_mem (j : Fin 31) : (lambdaTable1 j).Mem (lambda (damping 1) (frequency j)) := by
  rw [← lambdaTable1_calc]
  exact lambdaBox_mem 1 j
lemma phaseHTable1_calc (j : Fin 31) : wavePhaseBox 1 1 j = phaseHTable1 j := by
  revert j
  decide +kernel
lemma phaseHTable1_mem (j : Fin 31) : (phaseHTable1 j).Mem (I*Real.pi*zeta (damping 1) (damping 1) (frequency j)) := by
  rw [← phaseHTable1_calc]
  exact wavePhaseBox_mem 1 1 j
lemma lambdaTable_mem (q : Fin 2) (j : Fin 31) : (lambdaTable q j).Mem (lambda (damping q) (frequency j)) := by
  fin_cases q
  · exact lambdaTable0_mem j
  · exact lambdaTable1_mem j
lemma phaseHTable_mem (q : Fin 2) (j : Fin 31) :
    (phaseHTable q j).Mem (I*Real.pi*zeta (damping q) (damping 1) (frequency j)) := by
  fin_cases q
  · exact phaseHTable0_mem j
  · exact phaseHTable1_mem j
lemma QTable_mem (a : Fin 10) : (QTable a).Mem (Q (finiteNode a)) := by
  fin_cases a
  · exact QBox1_mem
  · exact QBox3_mem
  · exact QBox4_mem
  · exact QBox7_mem
  · exact QBox9_mem
  · exact QBox12_mem
  · exact QBox13_mem
  · exact QBox16_mem
  · exact QBox19_mem
  · exact QBox21_mem
lemma DTable_mem (a : Fin 10) : (DTable a).Mem (D (finiteNode a)) := by
  fin_cases a
  · exact DBox1_mem
  · exact DBox3_mem
  · exact DBox4_mem
  · exact DBox7_mem
  · exact DBox9_mem
  · exact DBox12_mem
  · exact DBox13_mem
  · exact DBox16_mem
  · exact DBox19_mem
  · exact DBox21_mem
lemma QTable_pos (n : Fin 10) : 0 < (QTable n).lo := by
  revert n
  decide +kernel

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveJetsData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma jetMultiplierBox_mem (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetMultiplierBox q i j).Mem
    (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j)) := by
  let n : Fin 10 := ⟨i.val/2,by omega⟩
  have hq := CI.mem_ofReal (RI.mem_invPos (QTable_mem n) (QTable_pos n))
  have he := waveExpTable_mem_eu q n j
  have hp := phaseHTable_mem q j
  have hh := CI.mem_mul (CI.mem_mul hq (lambdaTable_mem q j)) he
  unfold jetMultiplier transformedWave
  rw [← mul_assoc,← Complex.ofReal_inv]
  change ((jetMultiplierBox q i j)).Mem _
  unfold jetMultiplierBox
  split_ifs with hi
  · simpa only [damping, Fin.val_one, one_ne_zero, ↓reduceIte, Fin.val_mk, hi,
      Complex.ofReal_intCast, Int.cast_neg, Int.cast_ofNat, Nat.cast_one, Int.cast_one] using CI.mem_mul hh (CI.mem_point (-1))
  · simpa only [damping, Fin.val_one, one_ne_zero, ↓reduceIte, Fin.val_mk, hi] using
      CI.mem_mul hh (CI.mem_sub (CI.mem_ofReal (DTable_mem n)) hp)

lemma jetTable0_0_calc (j : Fin 31) : jetMultiplierBox 0 0 j = jetTable0_0 j := by
  revert j
  decide +kernel
lemma jetTable0_0_mem (j : Fin 31) : (jetTable0_0 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨0,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_0_calc]
  exact jetMultiplierBox_mem 0 0 j
lemma jetTable0_1_calc (j : Fin 31) : jetMultiplierBox 0 1 j = jetTable0_1 j := by
  revert j
  decide +kernel
lemma jetTable0_1_mem (j : Fin 31) : (jetTable0_1 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨0,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_1_calc]
  exact jetMultiplierBox_mem 0 1 j
lemma jetTable0_2_calc (j : Fin 31) : jetMultiplierBox 0 2 j = jetTable0_2 j := by
  revert j
  decide +kernel
lemma jetTable0_2_mem (j : Fin 31) : (jetTable0_2 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨1,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_2_calc]
  exact jetMultiplierBox_mem 0 2 j
lemma jetTable0_3_calc (j : Fin 31) : jetMultiplierBox 0 3 j = jetTable0_3 j := by
  revert j
  decide +kernel
lemma jetTable0_3_mem (j : Fin 31) : (jetTable0_3 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨1,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_3_calc]
  exact jetMultiplierBox_mem 0 3 j
lemma jetTable0_4_calc (j : Fin 31) : jetMultiplierBox 0 4 j = jetTable0_4 j := by
  revert j
  decide +kernel
lemma jetTable0_4_mem (j : Fin 31) : (jetTable0_4 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨2,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_4_calc]
  exact jetMultiplierBox_mem 0 4 j
lemma jetTable0_5_calc (j : Fin 31) : jetMultiplierBox 0 5 j = jetTable0_5 j := by
  revert j
  decide +kernel
lemma jetTable0_5_mem (j : Fin 31) : (jetTable0_5 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨2,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_5_calc]
  exact jetMultiplierBox_mem 0 5 j
lemma jetTable0_6_calc (j : Fin 31) : jetMultiplierBox 0 6 j = jetTable0_6 j := by
  revert j
  decide +kernel
lemma jetTable0_6_mem (j : Fin 31) : (jetTable0_6 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_6_calc]
  exact jetMultiplierBox_mem 0 6 j
lemma jetTable0_7_calc (j : Fin 31) : jetMultiplierBox 0 7 j = jetTable0_7 j := by
  revert j
  decide +kernel
lemma jetTable0_7_mem (j : Fin 31) : (jetTable0_7 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_7_calc]
  exact jetMultiplierBox_mem 0 7 j
lemma jetTable0_8_calc (j : Fin 31) : jetMultiplierBox 0 8 j = jetTable0_8 j := by
  revert j
  decide +kernel
lemma jetTable0_8_mem (j : Fin 31) : (jetTable0_8 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨4,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_8_calc]
  exact jetMultiplierBox_mem 0 8 j
lemma jetTable0_9_calc (j : Fin 31) : jetMultiplierBox 0 9 j = jetTable0_9 j := by
  revert j
  decide +kernel
lemma jetTable0_9_mem (j : Fin 31) : (jetTable0_9 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨4,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_9_calc]
  exact jetMultiplierBox_mem 0 9 j
lemma jetTable0_10_calc (j : Fin 31) : jetMultiplierBox 0 10 j = jetTable0_10 j := by
  revert j
  decide +kernel
lemma jetTable0_10_mem (j : Fin 31) : (jetTable0_10 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨5,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_10_calc]
  exact jetMultiplierBox_mem 0 10 j
lemma jetTable0_11_calc (j : Fin 31) : jetMultiplierBox 0 11 j = jetTable0_11 j := by
  revert j
  decide +kernel
lemma jetTable0_11_mem (j : Fin 31) : (jetTable0_11 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨5,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_11_calc]
  exact jetMultiplierBox_mem 0 11 j
lemma jetTable0_12_calc (j : Fin 31) : jetMultiplierBox 0 12 j = jetTable0_12 j := by
  revert j
  decide +kernel
lemma jetTable0_12_mem (j : Fin 31) : (jetTable0_12 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨6,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_12_calc]
  exact jetMultiplierBox_mem 0 12 j
lemma jetTable0_13_calc (j : Fin 31) : jetMultiplierBox 0 13 j = jetTable0_13 j := by
  revert j
  decide +kernel
lemma jetTable0_13_mem (j : Fin 31) : (jetTable0_13 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨6,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_13_calc]
  exact jetMultiplierBox_mem 0 13 j
lemma jetTable0_14_calc (j : Fin 31) : jetMultiplierBox 0 14 j = jetTable0_14 j := by
  revert j
  decide +kernel
lemma jetTable0_14_mem (j : Fin 31) : (jetTable0_14 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨7,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_14_calc]
  exact jetMultiplierBox_mem 0 14 j
lemma jetTable0_15_calc (j : Fin 31) : jetMultiplierBox 0 15 j = jetTable0_15 j := by
  revert j
  decide +kernel
lemma jetTable0_15_mem (j : Fin 31) : (jetTable0_15 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨7,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_15_calc]
  exact jetMultiplierBox_mem 0 15 j
lemma jetTable0_16_calc (j : Fin 31) : jetMultiplierBox 0 16 j = jetTable0_16 j := by
  revert j
  decide +kernel
lemma jetTable0_16_mem (j : Fin 31) : (jetTable0_16 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨8,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_16_calc]
  exact jetMultiplierBox_mem 0 16 j
lemma jetTable0_17_calc (j : Fin 31) : jetMultiplierBox 0 17 j = jetTable0_17 j := by
  revert j
  decide +kernel
lemma jetTable0_17_mem (j : Fin 31) : (jetTable0_17 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨8,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_17_calc]
  exact jetMultiplierBox_mem 0 17 j
lemma jetTable0_18_calc (j : Fin 31) : jetMultiplierBox 0 18 j = jetTable0_18 j := by
  revert j
  decide +kernel
lemma jetTable0_18_mem (j : Fin 31) : (jetTable0_18 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨9,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_18_calc]
  exact jetMultiplierBox_mem 0 18 j
lemma jetTable0_19_calc (j : Fin 31) : jetMultiplierBox 0 19 j = jetTable0_19 j := by
  revert j
  decide +kernel
lemma jetTable0_19_mem (j : Fin 31) : (jetTable0_19 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨9,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable0_19_calc]
  exact jetMultiplierBox_mem 0 19 j
lemma jetTable1_0_calc (j : Fin 31) : jetMultiplierBox 1 0 j = jetTable1_0 j := by
  revert j
  decide +kernel
lemma jetTable1_0_mem (j : Fin 31) : (jetTable1_0 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨0,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_0_calc]
  exact jetMultiplierBox_mem 1 0 j
lemma jetTable1_1_calc (j : Fin 31) : jetMultiplierBox 1 1 j = jetTable1_1 j := by
  revert j
  decide +kernel
lemma jetTable1_1_mem (j : Fin 31) : (jetTable1_1 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨0,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_1_calc]
  exact jetMultiplierBox_mem 1 1 j
lemma jetTable1_2_calc (j : Fin 31) : jetMultiplierBox 1 2 j = jetTable1_2 j := by
  revert j
  decide +kernel
lemma jetTable1_2_mem (j : Fin 31) : (jetTable1_2 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨1,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_2_calc]
  exact jetMultiplierBox_mem 1 2 j
lemma jetTable1_3_calc (j : Fin 31) : jetMultiplierBox 1 3 j = jetTable1_3 j := by
  revert j
  decide +kernel
lemma jetTable1_3_mem (j : Fin 31) : (jetTable1_3 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨1,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_3_calc]
  exact jetMultiplierBox_mem 1 3 j
lemma jetTable1_4_calc (j : Fin 31) : jetMultiplierBox 1 4 j = jetTable1_4 j := by
  revert j
  decide +kernel
lemma jetTable1_4_mem (j : Fin 31) : (jetTable1_4 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨2,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_4_calc]
  exact jetMultiplierBox_mem 1 4 j
lemma jetTable1_5_calc (j : Fin 31) : jetMultiplierBox 1 5 j = jetTable1_5 j := by
  revert j
  decide +kernel
lemma jetTable1_5_mem (j : Fin 31) : (jetTable1_5 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨2,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_5_calc]
  exact jetMultiplierBox_mem 1 5 j
lemma jetTable1_6_calc (j : Fin 31) : jetMultiplierBox 1 6 j = jetTable1_6 j := by
  revert j
  decide +kernel
lemma jetTable1_6_mem (j : Fin 31) : (jetTable1_6 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨3,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_6_calc]
  exact jetMultiplierBox_mem 1 6 j
lemma jetTable1_7_calc (j : Fin 31) : jetMultiplierBox 1 7 j = jetTable1_7 j := by
  revert j
  decide +kernel
lemma jetTable1_7_mem (j : Fin 31) : (jetTable1_7 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_7_calc]
  exact jetMultiplierBox_mem 1 7 j
lemma jetTable1_8_calc (j : Fin 31) : jetMultiplierBox 1 8 j = jetTable1_8 j := by
  revert j
  decide +kernel
lemma jetTable1_8_mem (j : Fin 31) : (jetTable1_8 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨4,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_8_calc]
  exact jetMultiplierBox_mem 1 8 j
lemma jetTable1_9_calc (j : Fin 31) : jetMultiplierBox 1 9 j = jetTable1_9 j := by
  revert j
  decide +kernel
lemma jetTable1_9_mem (j : Fin 31) : (jetTable1_9 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨4,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_9_calc]
  exact jetMultiplierBox_mem 1 9 j
lemma jetTable1_10_calc (j : Fin 31) : jetMultiplierBox 1 10 j = jetTable1_10 j := by
  revert j
  decide +kernel
lemma jetTable1_10_mem (j : Fin 31) : (jetTable1_10 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨5,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_10_calc]
  exact jetMultiplierBox_mem 1 10 j
lemma jetTable1_11_calc (j : Fin 31) : jetMultiplierBox 1 11 j = jetTable1_11 j := by
  revert j
  decide +kernel
lemma jetTable1_11_mem (j : Fin 31) : (jetTable1_11 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨5,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_11_calc]
  exact jetMultiplierBox_mem 1 11 j
lemma jetTable1_12_calc (j : Fin 31) : jetMultiplierBox 1 12 j = jetTable1_12 j := by
  revert j
  decide +kernel
lemma jetTable1_12_mem (j : Fin 31) : (jetTable1_12 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨6,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_12_calc]
  exact jetMultiplierBox_mem 1 12 j
lemma jetTable1_13_calc (j : Fin 31) : jetMultiplierBox 1 13 j = jetTable1_13 j := by
  revert j
  decide +kernel
lemma jetTable1_13_mem (j : Fin 31) : (jetTable1_13 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨6,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_13_calc]
  exact jetMultiplierBox_mem 1 13 j
lemma jetTable1_14_calc (j : Fin 31) : jetMultiplierBox 1 14 j = jetTable1_14 j := by
  revert j
  decide +kernel
lemma jetTable1_14_mem (j : Fin 31) : (jetTable1_14 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨7,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_14_calc]
  exact jetMultiplierBox_mem 1 14 j
lemma jetTable1_15_calc (j : Fin 31) : jetMultiplierBox 1 15 j = jetTable1_15 j := by
  revert j
  decide +kernel
lemma jetTable1_15_mem (j : Fin 31) : (jetTable1_15 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨7,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_15_calc]
  exact jetMultiplierBox_mem 1 15 j
lemma jetTable1_16_calc (j : Fin 31) : jetMultiplierBox 1 16 j = jetTable1_16 j := by
  revert j
  decide +kernel
lemma jetTable1_16_mem (j : Fin 31) : (jetTable1_16 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨8,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_16_calc]
  exact jetMultiplierBox_mem 1 16 j
lemma jetTable1_17_calc (j : Fin 31) : jetMultiplierBox 1 17 j = jetTable1_17 j := by
  revert j
  decide +kernel
lemma jetTable1_17_mem (j : Fin 31) : (jetTable1_17 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨8,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_17_calc]
  exact jetMultiplierBox_mem 1 17 j
lemma jetTable1_18_calc (j : Fin 31) : jetMultiplierBox 1 18 j = jetTable1_18 j := by
  revert j
  decide +kernel
lemma jetTable1_18_mem (j : Fin 31) : (jetTable1_18 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨9,by norm_num⟩) ⟨0,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_18_calc]
  exact jetMultiplierBox_mem 1 18 j
lemma jetTable1_19_calc (j : Fin 31) : jetMultiplierBox 1 19 j = jetTable1_19 j := by
  revert j
  decide +kernel
lemma jetTable1_19_mem (j : Fin 31) : (jetTable1_19 j).Mem
    (jetMultiplier (damping 1) H (finiteNode ⟨9,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  rw [← jetTable1_19_calc]
  exact jetMultiplierBox_mem 1 19 j
lemma jetTable_mem (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetTable q i j).Mem
    (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j)) := by
  fin_cases q <;> fin_cases i
  · exact jetTable0_0_mem j
  · exact jetTable0_1_mem j
  · exact jetTable0_2_mem j
  · exact jetTable0_3_mem j
  · exact jetTable0_4_mem j
  · exact jetTable0_5_mem j
  · exact jetTable0_6_mem j
  · exact jetTable0_7_mem j
  · exact jetTable0_8_mem j
  · exact jetTable0_9_mem j
  · exact jetTable0_10_mem j
  · exact jetTable0_11_mem j
  · exact jetTable0_12_mem j
  · exact jetTable0_13_mem j
  · exact jetTable0_14_mem j
  · exact jetTable0_15_mem j
  · exact jetTable0_16_mem j
  · exact jetTable0_17_mem j
  · exact jetTable0_18_mem j
  · exact jetTable0_19_mem j
  · exact jetTable1_0_mem j
  · exact jetTable1_1_mem j
  · exact jetTable1_2_mem j
  · exact jetTable1_3_mem j
  · exact jetTable1_4_mem j
  · exact jetTable1_5_mem j
  · exact jetTable1_6_mem j
  · exact jetTable1_7_mem j
  · exact jetTable1_8_mem j
  · exact jetTable1_9_mem j
  · exact jetTable1_10_mem j
  · exact jetTable1_11_mem j
  · exact jetTable1_12_mem j
  · exact jetTable1_13_mem j
  · exact jetTable1_14_mem j
  · exact jetTable1_15_mem j
  · exact jetTable1_16_mem j
  · exact jetTable1_17_mem j
  · exact jetTable1_18_mem j
  · exact jetTable1_19_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_JetMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fullJetBox_mem_eu_oai (i : Fin 20) (col : Fin 23) : (fullJetBox i col).Mem (fullJetMatrix i col) := by
  have hh := (CI.mem_sum (fun j => CI.mem_mul (jetTable_mem (if col.val=22 then 0 else 1) i j)
    (columnTable_mem_eu col j))).1
  by_cases hc : col.val=22
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh
  · simpa [fullJetBox, fullJetMatrix, jet, damping, hc] using hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu_oai
