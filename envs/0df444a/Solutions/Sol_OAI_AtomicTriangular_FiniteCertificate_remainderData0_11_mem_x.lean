-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:43:21.233656+00:00
-- url     : https://prove2.me/submissions/b504c348-5dac-4dcc-87df-f4c10c2a936d

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorPhase0_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorPhase1_1_mem_x

section
-- module Solutions.OAIQ250_TR.Triangular_Certificate_WaveIntervals
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

lemma RI.mem_sqrt {a r : RI} {x : ℝ} (hx : a.Mem x) (h₀ : 0 ≤ x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.lo)
    (hr₂ : scale * a.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem (Real.sqrt x) := by
  have hs := Real.sq_sqrt h₀
  have hp := Real.sqrt_nonneg x
  have hrl : (0:ℝ) ≤ r.lo := by exact_mod_cast hr₀
  have hrh : (0:ℝ) ≤ r.hi := by exact_mod_cast hr₃
  have hrls : (r.lo:ℝ) * r.lo ≤ (scale:ℝ) * max (0:ℝ) (a.lo:ℝ) := by exact_mod_cast hr₁
  have hrhs : (scale:ℝ) * a.hi ≤ (r.hi:ℝ) * r.hi := by exact_mod_cast hr₂
  have hsl := mul_le_mul_of_nonneg_left (max_le (mul_nonneg scale_pos.le h₀) hx.1) scale_pos.le
  have hsh := mul_le_mul_of_nonneg_left hx.2 scale_pos.le
  have he : ((scale:ℝ) * Real.sqrt x)^2 = (scale:ℝ) * ((scale:ℝ)*x) := by
    rw [mul_pow, hs]
    ring
  constructor <;> nlinarith [mul_nonneg scale_pos.le hp]

lemma CI.mem_norm {a : CI} {r : RI} {x : ℂ} (hx : a.Mem x)
    (hr₀ : 0 ≤ r.lo) (hr₁ : r.lo * r.lo ≤ scale * max 0 a.normSq.lo)
    (hr₂ : scale * a.normSq.hi ≤ r.hi * r.hi) (hr₃ : 0 ≤ r.hi) :
    r.Mem ‖x‖ := by
  have hh := RI.mem_sqrt (CI.mem_normSq hx) (Complex.normSq_nonneg x) hr₀ hr₁ hr₂ hr₃
  simpa [Complex.normSq_eq_norm_sq] using hh

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

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex

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
lemma xwaveBox_mem (q : Fin 2) (j : Fin 31) :
    (xwaveBox q j).Mem (Xwave (damping q) (frequency j)) := by
  unfold Xwave
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_divNat (RI.mem_point 4) (by norm_num : 0<(3:ℕ)))
    (RI.mem_invPos (denBox_mem q j) (denBox_pos q j))

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
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorPhase
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
lemma taylorPhaseTable_mem (q br : Fin 2) (j : Fin 31) :
    (taylorPhaseTable q br j).Mem (taylorPhase q br (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact taylorPhase0_0_mem_x j
  · exact taylorPhase0_1_mem j
  · exact taylorPhase1_0_mem j
  · exact taylorPhase1_1_mem_x j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma taylorNorm00_check (j : Fin 31) : 0≤(taylorNorm00 j).lo ∧ (taylorNorm00 j).lo*(taylorNorm00 j).lo ≤ scale*max 0 (taylorPhaseTable 0 0 j).normSq.lo ∧ scale*(taylorPhaseTable 0 0 j).normSq.hi ≤ (taylorNorm00 j).hi*(taylorNorm00 j).hi ∧ 0≤(taylorNorm00 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm00_mem (j : Fin 31) : (taylorNorm00 j).Mem ‖taylorPhase 0 0 (frequency j)‖ := by
  have hh := taylorNorm00_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm01_check (j : Fin 31) : 0≤(taylorNorm01 j).lo ∧ (taylorNorm01 j).lo*(taylorNorm01 j).lo ≤ scale*max 0 (taylorPhaseTable 0 1 j).normSq.lo ∧ scale*(taylorPhaseTable 0 1 j).normSq.hi ≤ (taylorNorm01 j).hi*(taylorNorm01 j).hi ∧ 0≤(taylorNorm01 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm01_mem (j : Fin 31) : (taylorNorm01 j).Mem ‖taylorPhase 0 1 (frequency j)‖ := by
  have hh := taylorNorm01_check j
  exact CI.mem_norm (taylorPhaseTable_mem 0 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm10_check (j : Fin 31) : 0≤(taylorNorm10 j).lo ∧ (taylorNorm10 j).lo*(taylorNorm10 j).lo ≤ scale*max 0 (taylorPhaseTable 1 0 j).normSq.lo ∧ scale*(taylorPhaseTable 1 0 j).normSq.hi ≤ (taylorNorm10 j).hi*(taylorNorm10 j).hi ∧ 0≤(taylorNorm10 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm10_mem (j : Fin 31) : (taylorNorm10 j).Mem ‖taylorPhase 1 0 (frequency j)‖ := by
  have hh := taylorNorm10_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNorm11_check (j : Fin 31) : 0≤(taylorNorm11 j).lo ∧ (taylorNorm11 j).lo*(taylorNorm11 j).lo ≤ scale*max 0 (taylorPhaseTable 1 1 j).normSq.lo ∧ scale*(taylorPhaseTable 1 1 j).normSq.hi ≤ (taylorNorm11 j).hi*(taylorNorm11 j).hi ∧ 0≤(taylorNorm11 j).hi := by
  revert j
  decide +kernel
lemma taylorNorm11_mem (j : Fin 31) : (taylorNorm11 j).Mem ‖taylorPhase 1 1 (frequency j)‖ := by
  have hh := taylorNorm11_check j
  exact CI.mem_norm (taylorPhaseTable_mem 1 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma taylorNormTable_mem (q br : Fin 2) (j : Fin 31) : (taylorNormTable q br j).Mem ‖taylorPhase q br (frequency j)‖ := by
  fin_cases q <;> fin_cases br
  · exact taylorNorm00_mem j
  · exact taylorNorm01_mem j
  · exact taylorNorm10_mem j
  · exact taylorNorm11_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderData0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData0_11_pre (j : Fin 31) : (remainderExpInput 1 1 0 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 0).mul (taylorNormTable 1 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData0_11_mem_x_oai (j : Fin 31) : (remainderData0_11 j).Mem (remainderWave 1 1 (nearNode 0) (nearRadius 0) (frequency j)) := by
  rw [← remainderData0_11_calc_x]
  exact remainderBox_mem_x 1 1 0 j (taylorNormTable_mem 1 1 j) (remainderData0_11_pre j).1 (remainderData0_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderData0_11_mem_x_oai
