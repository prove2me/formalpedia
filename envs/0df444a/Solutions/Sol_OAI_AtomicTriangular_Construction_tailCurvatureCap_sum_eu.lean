-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:02:28.396101+00:00
-- url     : https://prove2.me/submissions/93382561-b445-4cd2-9c03-db3eb91aede8

import Mathlib
import Definitions.Def_OAIQ334E021
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData00_0_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData00_1_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData00_2_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData00_3_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureData00_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureTable01_mem_eu

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
-- module Solutions.OAIQ334_EU.Triangular_Construction_CurvatureAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0 ≤ curvatureWave q br s t := by
  unfold curvatureWave; positivity
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_CurvatureData00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureData00_4_pre (j : Fin 31) : (curvatureExpInput 0 0 4 j).normSq.hi ≤ scale*1024^2 := by
  revert j
  decide +kernel
lemma curvatureData00_4_mem (j : Fin 31) : (curvatureData00_4 j).Mem (curvatureWave 0 0 (curvaturePoint 4) (frequency j)) := by
  rw [← curvatureData00_4_calc_eu]
  exact curvatureBox_mem_eu 0 0 4 j (curvatureData00_4_pre j)
lemma curvatureTable00_mem (i : Fin 5) (j : Fin 31) : (curvatureTable00 i j).Mem (curvatureWave 0 0 (curvaturePoint i) (frequency j)) := by
  fin_cases i
  · exact curvatureData00_0_mem_eu j
  · exact curvatureData00_1_mem_eu j
  · exact curvatureData00_2_mem_eu j
  · exact curvatureData00_3_mem_eu j
  · exact curvatureData00_4_mem j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_CurvatureSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma curvatureTail0_calc : ((curvatureTable00 0 30).add (curvatureTable01 0 15)).mul (RI.point 60)=curvatureTail0 := by decide +kernel
lemma curvatureTail0_bound : rawTailCurvature 0 < (26500:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 0 30) (curvatureTable01_mem_eu 0 15)) (RI.mem_point 60)
  rw [curvatureTail0_calc] at hh
  have hh' := ri_mem_lt hh 26500 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail1_calc : ((curvatureTable00 1 30).add (curvatureTable01 1 30)).mul (RI.point 60)=curvatureTail1 := by decide +kernel
lemma curvatureTail1_bound : rawTailCurvature 1 < (1160:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 1 30) (curvatureTable01_mem_eu 1 30)) (RI.mem_point 60)
  rw [curvatureTail1_calc] at hh
  have hh' := ri_mem_lt hh 1160 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail2_calc : ((curvatureTable00 2 30).add (curvatureTable01 2 30)).mul (RI.point 60)=curvatureTail2 := by decide +kernel
lemma curvatureTail2_bound : rawTailCurvature 2 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 2 30) (curvatureTable01_mem_eu 2 30)) (RI.mem_point 60)
  rw [curvatureTail2_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail3_calc : ((curvatureTable00 3 30).add (curvatureTable01 3 30)).mul (RI.point 60)=curvatureTail3 := by decide +kernel
lemma curvatureTail3_bound : rawTailCurvature 3 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 3 30) (curvatureTable01_mem_eu 3 30)) (RI.mem_point 60)
  rw [curvatureTail3_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
lemma curvatureTail4_calc : ((curvatureTable00 4 30).add (curvatureTable01 4 30)).mul (RI.point 60)=curvatureTail4 := by decide +kernel
lemma curvatureTail4_bound : rawTailCurvature 4 < (800:ℝ) := by
  have hh := RI.mem_mul (RI.mem_add (curvatureTable00_mem 4 30) (curvatureTable01_mem_eu 4 30)) (RI.mem_point 60)
  rw [curvatureTail4_calc] at hh
  have hh' := ri_mem_lt hh 800 1 (by norm_num) (by decide +kernel)
  simpa [rawTailCurvature,mul_comm] using hh'
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_CurvatureEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma tailCurvatureCap_nonneg (br : Fin 2) (i : Fin 5) : 0≤tailCurvatureCap br i := curvatureWave_nonneg _ _ _ _
lemma tailCurvatureCap_sum_eu_oai (i : Fin 5) :
    (119/2)*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)≤tailCurvatureEnvelope i := by
  have he : 60*(tailCurvatureCap 0 i+tailCurvatureCap 1 i)=rawTailCurvature i := by
    fin_cases i <;> (first | (simp [tailCurvatureCap,rawTailCurvature,frequency]; all_goals first | (norm_num [tailCurvatureCap,rawTailCurvature,frequency]; done) | rfl | decide) | (norm_num [tailCurvatureCap,rawTailCurvature,frequency]; done) | norm_num [tailCurvatureCap,rawTailCurvature,frequency])
  have hb : rawTailCurvature i<tailCurvatureEnvelope i := by
    fin_cases i
    · exact curvatureTail0_bound
    · exact curvatureTail1_bound
    · exact curvatureTail2_bound
    · exact curvatureTail3_bound
    · exact curvatureTail4_bound
  nlinarith [tailCurvatureCap_nonneg 0 i,tailCurvatureCap_nonneg 1 i]
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_eu_oai := @OAI.AtomicTriangular.Construction.tailCurvatureCap_sum_eu_oai
