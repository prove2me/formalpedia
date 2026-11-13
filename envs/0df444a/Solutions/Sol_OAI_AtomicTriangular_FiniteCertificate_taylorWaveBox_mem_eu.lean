-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:01:09.432793+00:00
-- url     : https://prove2.me/submissions/d70491c7-8c74-4d24-a92e-1e561cd3c363

import Mathlib
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_0_9_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp0_1_9_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_0_9_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_12_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_13_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_4_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_7_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorExp1_1_9_mem_eu

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
lemma lambdaTable1_calc (j : Fin 31) : lambdaBox 1 j = lambdaTable1 j := by
  revert j
  decide +kernel
lemma lambdaTable1_mem (j : Fin 31) : (lambdaTable1 j).Mem (lambda (damping 1) (frequency j)) := by
  rw [← lambdaTable1_calc]
  exact lambdaBox_mem 1 j
lemma lambdaTable_mem (q : Fin 2) (j : Fin 31) : (lambdaTable q j).Mem (lambda (damping q) (frequency j)) := by
  fin_cases q
  · exact lambdaTable0_mem j
  · exact lambdaTable1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorPhaseBox_mem (q branch : Fin 2) (j : Fin 31) :
    (taylorPhaseBox q branch j).Mem (taylorPhase q branch (frequency j)) := by
  unfold taylorPhaseBox taylorPhase
  split_ifs
  · exact CI.mem_sub (CI.mem_mul (CI.mem_mul CI.mem_imag (CI.mem_ofReal piBox_mem)) (CI.mem_ofReal (realFrequencyBox_mem j)))
      (CI.mem_ofReal (RI.mem_mul piBox_mem (RI.mem_sub (dampingBox_mem q) (dampingBox_mem 0))))
  · exact wavePhaseBox_mem q 0 j

lemma taylorPhase0_0_calc (j : Fin 31) : taylorPhaseBox 0 0 j = taylorPhase0_0 j := by
  revert j
  decide +kernel
lemma taylorPhase0_0_mem (j : Fin 31) : (taylorPhase0_0 j).Mem (taylorPhase 0 0 (frequency j)) := by
  rw [← taylorPhase0_0_calc]
  exact taylorPhaseBox_mem 0 0 j
lemma taylorPhase0_1_calc (j : Fin 31) : taylorPhaseBox 0 1 j = taylorPhase0_1 j := by
  revert j
  decide +kernel
lemma taylorPhase0_1_mem (j : Fin 31) : (taylorPhase0_1 j).Mem (taylorPhase 0 1 (frequency j)) := by
  rw [← taylorPhase0_1_calc]
  exact taylorPhaseBox_mem 0 1 j
lemma taylorPhase1_0_calc (j : Fin 31) : taylorPhaseBox 1 0 j = taylorPhase1_0 j := by
  revert j
  decide +kernel
lemma taylorPhase1_0_mem (j : Fin 31) : (taylorPhase1_0 j).Mem (taylorPhase 1 0 (frequency j)) := by
  rw [← taylorPhase1_0_calc]
  exact taylorPhaseBox_mem 1 0 j
lemma taylorPhase1_1_calc (j : Fin 31) : taylorPhaseBox 1 1 j = taylorPhase1_1 j := by
  revert j
  decide +kernel
lemma taylorPhase1_1_mem (j : Fin 31) : (taylorPhase1_1 j).Mem (taylorPhase 1 1 (frequency j)) := by
  rw [← taylorPhase1_1_calc]
  exact taylorPhaseBox_mem 1 1 j
lemma taylorPhaseTable_mem (q br : Fin 2) (j : Fin 31) :
    (taylorPhaseTable q br j).Mem (taylorPhase q br (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact taylorPhase0_0_mem j
  · exact taylorPhase0_1_mem j
  · exact taylorPhase1_0_mem j
  · exact taylorPhase1_1_mem j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorExpTable_mem (q br : Fin 2) (n : Fin 7) (j : Fin 31) :
    (taylorExpTable q br n j).Mem (exp (taylorPhase q br (frequency j)*(nearNode n:ℂ))) := by
  fin_cases q <;> fin_cases br <;> fin_cases n
  · exact taylorExp0_0_1_mem_eu j
  · exact taylorExp0_0_3_mem_eu j
  · exact taylorExp0_0_4_mem_eu j
  · exact taylorExp0_0_7_mem_eu j
  · exact taylorExp0_0_9_mem_eu j
  · exact taylorExp0_0_12_mem_eu j
  · exact taylorExp0_0_13_mem_eu j
  · exact taylorExp0_1_1_mem_eu j
  · exact taylorExp0_1_3_mem_eu j
  · exact taylorExp0_1_4_mem_eu j
  · exact taylorExp0_1_7_mem_eu j
  · exact taylorExp0_1_9_mem_eu j
  · exact taylorExp0_1_12_mem_eu j
  · exact taylorExp0_1_13_mem_eu j
  · exact taylorExp1_0_1_mem_eu j
  · exact taylorExp1_0_3_mem_eu j
  · exact taylorExp1_0_4_mem_eu j
  · exact taylorExp1_0_7_mem_eu j
  · exact taylorExp1_0_9_mem_eu j
  · exact taylorExp1_0_12_mem_eu j
  · exact taylorExp1_0_13_mem_eu j
  · exact taylorExp1_1_1_mem_eu j
  · exact taylorExp1_1_3_mem_eu j
  · exact taylorExp1_1_4_mem_eu j
  · exact taylorExp1_1_7_mem_eu j
  · exact taylorExp1_1_9_mem_eu j
  · exact taylorExp1_1_12_mem_eu j
  · exact taylorExp1_1_13_mem_eu j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorAmplitudeBox_mem (q br : Fin 2) (j : Fin 31) :
    (taylorAmplitudeBox q br j).Mem (taylorAmplitude q br (frequency j)) := by
  unfold taylorAmplitudeBox taylorAmplitude
  split_ifs
  · simpa using CI.mem_point 1
  · exact lambdaTable_mem q j

lemma taylorWaveBox_mem_eu_oai (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveBox q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  exact CI.mem_divNat (CI.mem_mul (CI.mem_mul (taylorAmplitudeBox_mem q br j) (taylorExpTable_mem q br n j))
    (CI.mem_pow (taylorPhaseTable_mem q br j) (l.val+2))) (Nat.factorial_pos _)

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu_oai
