-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:36:07.099753+00:00
-- url     : https://prove2.me/submissions/de4e70d9-f497-41e0-a160-8a305d09208a

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData1_10_mem_x

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

end
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_RemainderSums1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns1_0_calc (c : Fin 22) : RI.sum (fun j : Fin 31 => (remainderData1_10 j).mul (columnNormTable ⟨c.val,by omega⟩ j))=remainderColumns1_0 c := by
  revert c
  decide +kernel
lemma remainderColumns1_0_bound_x_oai (c : Fin 22) : rawRemainderColumn 0 1 c < (21/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData1_10_mem_x j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns1_0_calc] at hh
  have hb := ri_mem_lt hh 21 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x_oai
