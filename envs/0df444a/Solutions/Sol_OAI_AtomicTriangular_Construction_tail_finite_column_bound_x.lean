-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.tail_finite_column_bound_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:41:48.228232+00:00
-- url     : https://prove2.me/submissions/cfab27b6-6053-494d-b835-e0b14515f1d2

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X005
import Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_periodExpC_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_psiTableC_mem_x

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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

lemma decayBox_mem (q v : Fin 2) (j : Fin 31) :
    (decayBox q v j).Mem (frequencyDecay (damping q) (damping v) (frequency j)) := by
  have hh := RI.mem_neg (wavePhaseBox_mem q v j).1
  convert hh using 1
  · rfl
  · rw [wavePhase_re]
    unfold frequencyDecay
    ring

lemma decayExpBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31)
    (hh : (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).normSq.hi ≤ scale*1024^2) :
    (decayExpBox q v n j).Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)) :=
  ri_exp_mem (RI.mem_mul (RI.mem_neg (decayBox_mem q v j)) (RI.mem_point n)) hh

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm0_check (j : Fin 31) : 0≤(columnNorm0 j).lo ∧ (columnNorm0 j).lo*(columnNorm0 j).lo ≤ scale*max 0 (columnTable 0 j).normSq.lo ∧ scale*(columnTable 0 j).normSq.hi ≤ (columnNorm0 j).hi*(columnNorm0 j).hi ∧ 0≤(columnNorm0 j).hi := by
  revert j
  decide +kernel
lemma columnNorm0_mem (j : Fin 31) : (columnNorm0 j).Mem ‖finiteColumn 0 j‖ := by
  have hh := columnNorm0_check j
  exact CI.mem_norm (columnTable_mem_x 0 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm1_check (j : Fin 31) : 0≤(columnNorm1 j).lo ∧ (columnNorm1 j).lo*(columnNorm1 j).lo ≤ scale*max 0 (columnTable 1 j).normSq.lo ∧ scale*(columnTable 1 j).normSq.hi ≤ (columnNorm1 j).hi*(columnNorm1 j).hi ∧ 0≤(columnNorm1 j).hi := by
  revert j
  decide +kernel
lemma columnNorm1_mem (j : Fin 31) : (columnNorm1 j).Mem ‖finiteColumn 1 j‖ := by
  have hh := columnNorm1_check j
  exact CI.mem_norm (columnTable_mem_x 1 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm2_check (j : Fin 31) : 0≤(columnNorm2 j).lo ∧ (columnNorm2 j).lo*(columnNorm2 j).lo ≤ scale*max 0 (columnTable 2 j).normSq.lo ∧ scale*(columnTable 2 j).normSq.hi ≤ (columnNorm2 j).hi*(columnNorm2 j).hi ∧ 0≤(columnNorm2 j).hi := by
  revert j
  decide +kernel
lemma columnNorm2_mem (j : Fin 31) : (columnNorm2 j).Mem ‖finiteColumn 2 j‖ := by
  have hh := columnNorm2_check j
  exact CI.mem_norm (columnTable_mem_x 2 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm3_check (j : Fin 31) : 0≤(columnNorm3 j).lo ∧ (columnNorm3 j).lo*(columnNorm3 j).lo ≤ scale*max 0 (columnTable 3 j).normSq.lo ∧ scale*(columnTable 3 j).normSq.hi ≤ (columnNorm3 j).hi*(columnNorm3 j).hi ∧ 0≤(columnNorm3 j).hi := by
  revert j
  decide +kernel
lemma columnNorm3_mem (j : Fin 31) : (columnNorm3 j).Mem ‖finiteColumn 3 j‖ := by
  have hh := columnNorm3_check j
  exact CI.mem_norm (columnTable_mem_x 3 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm4_check (j : Fin 31) : 0≤(columnNorm4 j).lo ∧ (columnNorm4 j).lo*(columnNorm4 j).lo ≤ scale*max 0 (columnTable 4 j).normSq.lo ∧ scale*(columnTable 4 j).normSq.hi ≤ (columnNorm4 j).hi*(columnNorm4 j).hi ∧ 0≤(columnNorm4 j).hi := by
  revert j
  decide +kernel
lemma columnNorm4_mem (j : Fin 31) : (columnNorm4 j).Mem ‖finiteColumn 4 j‖ := by
  have hh := columnNorm4_check j
  exact CI.mem_norm (columnTable_mem_x 4 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm5_check (j : Fin 31) : 0≤(columnNorm5 j).lo ∧ (columnNorm5 j).lo*(columnNorm5 j).lo ≤ scale*max 0 (columnTable 5 j).normSq.lo ∧ scale*(columnTable 5 j).normSq.hi ≤ (columnNorm5 j).hi*(columnNorm5 j).hi ∧ 0≤(columnNorm5 j).hi := by
  revert j
  decide +kernel
lemma columnNorm5_mem (j : Fin 31) : (columnNorm5 j).Mem ‖finiteColumn 5 j‖ := by
  have hh := columnNorm5_check j
  exact CI.mem_norm (columnTable_mem_x 5 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm6_check (j : Fin 31) : 0≤(columnNorm6 j).lo ∧ (columnNorm6 j).lo*(columnNorm6 j).lo ≤ scale*max 0 (columnTable 6 j).normSq.lo ∧ scale*(columnTable 6 j).normSq.hi ≤ (columnNorm6 j).hi*(columnNorm6 j).hi ∧ 0≤(columnNorm6 j).hi := by
  revert j
  decide +kernel
lemma columnNorm6_mem (j : Fin 31) : (columnNorm6 j).Mem ‖finiteColumn 6 j‖ := by
  have hh := columnNorm6_check j
  exact CI.mem_norm (columnTable_mem_x 6 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm7_check (j : Fin 31) : 0≤(columnNorm7 j).lo ∧ (columnNorm7 j).lo*(columnNorm7 j).lo ≤ scale*max 0 (columnTable 7 j).normSq.lo ∧ scale*(columnTable 7 j).normSq.hi ≤ (columnNorm7 j).hi*(columnNorm7 j).hi ∧ 0≤(columnNorm7 j).hi := by
  revert j
  decide +kernel
lemma columnNorm7_mem (j : Fin 31) : (columnNorm7 j).Mem ‖finiteColumn 7 j‖ := by
  have hh := columnNorm7_check j
  exact CI.mem_norm (columnTable_mem_x 7 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm8_check (j : Fin 31) : 0≤(columnNorm8 j).lo ∧ (columnNorm8 j).lo*(columnNorm8 j).lo ≤ scale*max 0 (columnTable 8 j).normSq.lo ∧ scale*(columnTable 8 j).normSq.hi ≤ (columnNorm8 j).hi*(columnNorm8 j).hi ∧ 0≤(columnNorm8 j).hi := by
  revert j
  decide +kernel
lemma columnNorm8_mem (j : Fin 31) : (columnNorm8 j).Mem ‖finiteColumn 8 j‖ := by
  have hh := columnNorm8_check j
  exact CI.mem_norm (columnTable_mem_x 8 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm9_check (j : Fin 31) : 0≤(columnNorm9 j).lo ∧ (columnNorm9 j).lo*(columnNorm9 j).lo ≤ scale*max 0 (columnTable 9 j).normSq.lo ∧ scale*(columnTable 9 j).normSq.hi ≤ (columnNorm9 j).hi*(columnNorm9 j).hi ∧ 0≤(columnNorm9 j).hi := by
  revert j
  decide +kernel
lemma columnNorm9_mem (j : Fin 31) : (columnNorm9 j).Mem ‖finiteColumn 9 j‖ := by
  have hh := columnNorm9_check j
  exact CI.mem_norm (columnTable_mem_x 9 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm10_check (j : Fin 31) : 0≤(columnNorm10 j).lo ∧ (columnNorm10 j).lo*(columnNorm10 j).lo ≤ scale*max 0 (columnTable 10 j).normSq.lo ∧ scale*(columnTable 10 j).normSq.hi ≤ (columnNorm10 j).hi*(columnNorm10 j).hi ∧ 0≤(columnNorm10 j).hi := by
  revert j
  decide +kernel
lemma columnNorm10_mem (j : Fin 31) : (columnNorm10 j).Mem ‖finiteColumn 10 j‖ := by
  have hh := columnNorm10_check j
  exact CI.mem_norm (columnTable_mem_x 10 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm11_check (j : Fin 31) : 0≤(columnNorm11 j).lo ∧ (columnNorm11 j).lo*(columnNorm11 j).lo ≤ scale*max 0 (columnTable 11 j).normSq.lo ∧ scale*(columnTable 11 j).normSq.hi ≤ (columnNorm11 j).hi*(columnNorm11 j).hi ∧ 0≤(columnNorm11 j).hi := by
  revert j
  decide +kernel
lemma columnNorm11_mem (j : Fin 31) : (columnNorm11 j).Mem ‖finiteColumn 11 j‖ := by
  have hh := columnNorm11_check j
  exact CI.mem_norm (columnTable_mem_x 11 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm12_check (j : Fin 31) : 0≤(columnNorm12 j).lo ∧ (columnNorm12 j).lo*(columnNorm12 j).lo ≤ scale*max 0 (columnTable 12 j).normSq.lo ∧ scale*(columnTable 12 j).normSq.hi ≤ (columnNorm12 j).hi*(columnNorm12 j).hi ∧ 0≤(columnNorm12 j).hi := by
  revert j
  decide +kernel
lemma columnNorm12_mem (j : Fin 31) : (columnNorm12 j).Mem ‖finiteColumn 12 j‖ := by
  have hh := columnNorm12_check j
  exact CI.mem_norm (columnTable_mem_x 12 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm13_check (j : Fin 31) : 0≤(columnNorm13 j).lo ∧ (columnNorm13 j).lo*(columnNorm13 j).lo ≤ scale*max 0 (columnTable 13 j).normSq.lo ∧ scale*(columnTable 13 j).normSq.hi ≤ (columnNorm13 j).hi*(columnNorm13 j).hi ∧ 0≤(columnNorm13 j).hi := by
  revert j
  decide +kernel
lemma columnNorm13_mem (j : Fin 31) : (columnNorm13 j).Mem ‖finiteColumn 13 j‖ := by
  have hh := columnNorm13_check j
  exact CI.mem_norm (columnTable_mem_x 13 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm14_check (j : Fin 31) : 0≤(columnNorm14 j).lo ∧ (columnNorm14 j).lo*(columnNorm14 j).lo ≤ scale*max 0 (columnTable 14 j).normSq.lo ∧ scale*(columnTable 14 j).normSq.hi ≤ (columnNorm14 j).hi*(columnNorm14 j).hi ∧ 0≤(columnNorm14 j).hi := by
  revert j
  decide +kernel
lemma columnNorm14_mem (j : Fin 31) : (columnNorm14 j).Mem ‖finiteColumn 14 j‖ := by
  have hh := columnNorm14_check j
  exact CI.mem_norm (columnTable_mem_x 14 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm15_check (j : Fin 31) : 0≤(columnNorm15 j).lo ∧ (columnNorm15 j).lo*(columnNorm15 j).lo ≤ scale*max 0 (columnTable 15 j).normSq.lo ∧ scale*(columnTable 15 j).normSq.hi ≤ (columnNorm15 j).hi*(columnNorm15 j).hi ∧ 0≤(columnNorm15 j).hi := by
  revert j
  decide +kernel
lemma columnNorm15_mem (j : Fin 31) : (columnNorm15 j).Mem ‖finiteColumn 15 j‖ := by
  have hh := columnNorm15_check j
  exact CI.mem_norm (columnTable_mem_x 15 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm16_check (j : Fin 31) : 0≤(columnNorm16 j).lo ∧ (columnNorm16 j).lo*(columnNorm16 j).lo ≤ scale*max 0 (columnTable 16 j).normSq.lo ∧ scale*(columnTable 16 j).normSq.hi ≤ (columnNorm16 j).hi*(columnNorm16 j).hi ∧ 0≤(columnNorm16 j).hi := by
  revert j
  decide +kernel
lemma columnNorm16_mem (j : Fin 31) : (columnNorm16 j).Mem ‖finiteColumn 16 j‖ := by
  have hh := columnNorm16_check j
  exact CI.mem_norm (columnTable_mem_x 16 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm17_check (j : Fin 31) : 0≤(columnNorm17 j).lo ∧ (columnNorm17 j).lo*(columnNorm17 j).lo ≤ scale*max 0 (columnTable 17 j).normSq.lo ∧ scale*(columnTable 17 j).normSq.hi ≤ (columnNorm17 j).hi*(columnNorm17 j).hi ∧ 0≤(columnNorm17 j).hi := by
  revert j
  decide +kernel
lemma columnNorm17_mem (j : Fin 31) : (columnNorm17 j).Mem ‖finiteColumn 17 j‖ := by
  have hh := columnNorm17_check j
  exact CI.mem_norm (columnTable_mem_x 17 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm18_check (j : Fin 31) : 0≤(columnNorm18 j).lo ∧ (columnNorm18 j).lo*(columnNorm18 j).lo ≤ scale*max 0 (columnTable 18 j).normSq.lo ∧ scale*(columnTable 18 j).normSq.hi ≤ (columnNorm18 j).hi*(columnNorm18 j).hi ∧ 0≤(columnNorm18 j).hi := by
  revert j
  decide +kernel
lemma columnNorm18_mem (j : Fin 31) : (columnNorm18 j).Mem ‖finiteColumn 18 j‖ := by
  have hh := columnNorm18_check j
  exact CI.mem_norm (columnTable_mem_x 18 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm19_check (j : Fin 31) : 0≤(columnNorm19 j).lo ∧ (columnNorm19 j).lo*(columnNorm19 j).lo ≤ scale*max 0 (columnTable 19 j).normSq.lo ∧ scale*(columnTable 19 j).normSq.hi ≤ (columnNorm19 j).hi*(columnNorm19 j).hi ∧ 0≤(columnNorm19 j).hi := by
  revert j
  decide +kernel
lemma columnNorm19_mem (j : Fin 31) : (columnNorm19 j).Mem ‖finiteColumn 19 j‖ := by
  have hh := columnNorm19_check j
  exact CI.mem_norm (columnTable_mem_x 19 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm20_check (j : Fin 31) : 0≤(columnNorm20 j).lo ∧ (columnNorm20 j).lo*(columnNorm20 j).lo ≤ scale*max 0 (columnTable 20 j).normSq.lo ∧ scale*(columnTable 20 j).normSq.hi ≤ (columnNorm20 j).hi*(columnNorm20 j).hi ∧ 0≤(columnNorm20 j).hi := by
  revert j
  decide +kernel
lemma columnNorm20_mem (j : Fin 31) : (columnNorm20 j).Mem ‖finiteColumn 20 j‖ := by
  have hh := columnNorm20_check j
  exact CI.mem_norm (columnTable_mem_x 20 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm21_check (j : Fin 31) : 0≤(columnNorm21 j).lo ∧ (columnNorm21 j).lo*(columnNorm21 j).lo ≤ scale*max 0 (columnTable 21 j).normSq.lo ∧ scale*(columnTable 21 j).normSq.hi ≤ (columnNorm21 j).hi*(columnNorm21 j).hi ∧ 0≤(columnNorm21 j).hi := by
  revert j
  decide +kernel
lemma columnNorm21_mem (j : Fin 31) : (columnNorm21 j).Mem ‖finiteColumn 21 j‖ := by
  have hh := columnNorm21_check j
  exact CI.mem_norm (columnTable_mem_x 21 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
lemma columnNorm22_check (j : Fin 31) : 0≤(columnNorm22 j).lo ∧ (columnNorm22 j).lo*(columnNorm22 j).lo ≤ scale*max 0 (columnTable 22 j).normSq.lo ∧ scale*(columnTable 22 j).normSq.hi ≤ (columnNorm22 j).hi*(columnNorm22 j).hi ∧ 0≤(columnNorm22 j).hi := by
  revert j
  decide +kernel
lemma columnNorm22_mem (j : Fin 31) : (columnNorm22 j).Mem ‖finiteColumn 22 j‖ := by
  have hh := columnNorm22_check j
  exact CI.mem_norm (columnTable_mem_x 22 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNormTable_mem (c : Fin 23) (j : Fin 31) : (columnNormTable c j).Mem ‖finiteColumn c j‖ := by
  fin_cases c
  · exact columnNorm0_mem j
  · exact columnNorm1_mem j
  · exact columnNorm2_mem j
  · exact columnNorm3_mem j
  · exact columnNorm4_mem j
  · exact columnNorm5_mem j
  · exact columnNorm6_mem j
  · exact columnNorm7_mem j
  · exact columnNorm8_mem j
  · exact columnNorm9_mem j
  · exact columnNorm10_mem j
  · exact columnNorm11_mem j
  · exact columnNorm12_mem j
  · exact columnNorm13_mem j
  · exact columnNorm14_mem j
  · exact columnNorm15_mem j
  · exact columnNorm16_mem j
  · exact columnNorm17_mem j
  · exact columnNorm18_mem j
  · exact columnNorm19_mem j
  · exact columnNorm20_mem j
  · exact columnNorm21_mem j
  · exact columnNorm22_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma envelopePhase10_calc (j : Fin 31) : wavePhaseBox 1 0 j=envelopePhase10 j := by
  revert j
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSumsBase
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
-- module Solutions.OAIQ250_TR.Triangular_Envelope_EnvelopeSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma periodExpC_pre (j : Fin 31) : (CI.ofReal ((envelopePhase10 j).re.mul (RI.point 36))).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma periodExpC_mem (j : Fin 31) : (periodExpC j).Mem (Real.exp (-frequencyDecay (damping 1) (damping 0) (frequency j)*36)) := by
  rw [← periodExpC_calc_x]
  have hh := decayExpBox_mem 1 0 36 j
  unfold decayExpBox decayBox RI.neg at hh
  rw [envelopePhase10_calc] at hh
  simp only [neg_neg] at hh
  exact hh (periodExpC_pre j)
lemma periodDenC_pos (j : Fin 31) : 0<((RI.point 1).sub (periodExpC j)).lo := by
  revert j
  decide +kernel
lemma envelopeSumBoxC_calc (j : Fin 31) : (RI.sum (fun i : Fin 15 => psiTableC i j)).mul ((RI.point 1).sub (periodExpC j)).invPos=envelopeSumBoxC j := by
  revert j
  decide +kernel
lemma envelopeSumBoxC_mem (j : Fin 31) : (envelopeSumBoxC j).Mem (tailEnvelopeSum 1 0 j) := by
  rw [← envelopeSumBoxC_calc]
  exact RI.mem_mul (RI.mem_sum (fun i => psiTableC_mem_x i j))
    (RI.mem_invPos (RI.mem_sub ri1_mem (periodExpC_mem j)) (periodDenC_pos j))
lemma boundC_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (envelopeSumBoxC j).mul (columnNormTable ⟨c.val,by omega⟩ j))=boundC c := by
  revert c
  decide +kernel
lemma boundC_mem (c : Fin 22) : (boundC c).Mem (tailFiniteEnvelope c) := by
  rw [← boundC_calc]
  exact RI.mem_sum (fun j => RI.mem_mul (envelopeSumBoxC_mem j) (columnNormTable_mem _ j))
lemma tailFiniteEnvelope_bound (c : Fin 22) : tailFiniteEnvelope c < (7/1000000000000000:ℝ) := by
  apply ri_mem_lt (boundC_mem c) 7 1000000000000000 (by norm_num)
  revert c
  decide +kernel
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Envelope_KernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_finite_column_bound_x_oai (c : Fin 22) :
    (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15 := by
  exact (tail_atom_column_bounds_x 1 0 _).2.trans_lt (by norm_num [tailFiniteEnvelope,damping,H,h] at ⊢; simpa [tailFiniteEnvelope] using FiniteCertificate.tailFiniteEnvelope_bound c)
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.tail_finite_column_bound_x_oai := @OAI.AtomicTriangular.Construction.tail_finite_column_bound_x_oai
