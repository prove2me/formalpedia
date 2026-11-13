-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.remainderTable2_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:44.777304+00:00
-- url     : https://prove2.me/submissions/1a92d4d5-61c4-4c30-8f46-1bd0f794b861

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderColumns2_0_bound_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderColumns2_1_bound_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData2_00_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData2_01_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_eu

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
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeNorm2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnNorm22_check (j : Fin 31) : 0≤(columnNorm22 j).lo ∧ (columnNorm22 j).lo*(columnNorm22 j).lo ≤ scale*max 0 (columnTable 22 j).normSq.lo ∧ scale*(columnTable 22 j).normSq.hi ≤ (columnNorm22 j).hi*(columnNorm22 j).hi ∧ 0≤(columnNorm22 j).hi := by
  revert j
  decide +kernel
lemma columnNorm22_mem (j : Fin 31) : (columnNorm22 j).Mem ‖finiteColumn 22 j‖ := by
  have hh := columnNorm22_check j
  exact CI.mem_norm (columnTable_mem_eu 22 j) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_EnvelopeNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma fourierNorm_mem (j : Fin 31) : (columnNorm22 j).Mem ‖fourierCoeff j‖ := columnNorm22_mem j
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
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderData2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData2_01_pre (j : Fin 31) : (remainderExpInput 0 1 2 j).normSq.hi ≤ scale*1024^2 ∧ 0<((RI.point 1).sub (((nearRadiusBox 2).mul (taylorNormTable 0 1 j)).divNat 24)).lo := by
  revert j
  decide +kernel
lemma remainderData2_01_mem (j : Fin 31) : (remainderData2_01 j).Mem (remainderWave 0 1 (nearNode 2) (nearRadius 2) (frequency j)) := by
  rw [← remainderData2_01_calc_eu]
  exact remainderBox_mem_eu 0 1 2 j (taylorNormTable_mem_eu 0 1 j) (remainderData2_01_pre j).1 (remainderData2_01_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_RemainderSums2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst2_0_calc : RI.sum (fun j : Fin 31 => (remainderData2_00 j).mul (columnNorm22 j))=remainderConst2_0 := by decide +kernel
lemma remainderConst2_0_bound : rawRemainderConstant 0 2 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_00_mem_eu j) (fourierNorm_mem j))
  rw [remainderConst2_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst2_1_calc : RI.sum (fun j : Fin 31 => (remainderData2_01 j).mul (columnNorm22 j))=remainderConst2_1 := by decide +kernel
lemma remainderConst2_1_bound : rawRemainderConstant 1 2 < (1040413389772/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData2_01_mem j) (fourierNorm_mem j))
  rw [remainderConst2_1_calc] at hh
  have hb := ri_mem_lt hh 1040413389772 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable2_eu_oai (c d : Fin 22) : 3*(rawRemainderColumn 0 2 c+rawRemainderColumn 1 2 d)+(6/1000)*(rawRemainderConstant 0 2+rawRemainderConstant 1 2) < (75/10000000:ℝ) := by
  have h0 := remainderColumns2_0_bound_eu c
  have h1 := remainderColumns2_1_bound_eu d
  have h2 := remainderConst2_0_bound
  have h3 := remainderConst2_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.remainderTable2_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.remainderTable2_eu_oai
