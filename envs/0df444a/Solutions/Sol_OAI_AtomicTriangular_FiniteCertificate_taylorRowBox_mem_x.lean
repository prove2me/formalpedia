-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:24:10.841656+00:00
-- url     : https://prove2.me/submissions/19ab59e0-a7de-4481-9e79-a87606a79c6a

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X023
import Definitions.Def_OAIQ257X025
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_spectrumTable_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_2_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_3_9_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_4_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_5_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_0_6_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw0_1_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_0_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tw1_1_mem_x

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

end AtomicTriangular.Interval

end
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_3_16_calc (j : Fin 31) : taylorWaveBox 0 0 3 16 j = tw0_0_3_16 j := by
  revert j
  decide +kernel
lemma tw0_0_3_17_calc (j : Fin 31) : taylorWaveBox 0 0 3 17 j = tw0_0_3_17 j := by
  revert j
  decide +kernel
lemma tw0_0_3_18_calc (j : Fin 31) : taylorWaveBox 0 0 3 18 j = tw0_0_3_18 j := by
  revert j
  decide +kernel
lemma tw0_0_3_19_calc (j : Fin 31) : taylorWaveBox 0 0 3 19 j = tw0_0_3_19 j := by
  revert j
  decide +kernel
lemma tw0_0_3_20_calc (j : Fin 31) : taylorWaveBox 0 0 3 20 j = tw0_0_3_20 j := by
  revert j
  decide +kernel
lemma tw0_0_3_mem (l : Fin 21) (j : Fin 31) : (tw0_0_3 l j).Mem (taylorWave 0 0 (nearNode 3) l.val (frequency j)) := by
  have he : taylorWaveBox 0 0 3 l j = tw0_0_3 l j := by
    fin_cases l
    · exact tw0_0_3_0_calc_x j
    · exact tw0_0_3_1_calc_x j
    · exact tw0_0_3_2_calc_x j
    · exact tw0_0_3_3_calc_x j
    · exact tw0_0_3_4_calc_x j
    · exact tw0_0_3_5_calc_x j
    · exact tw0_0_3_6_calc_x j
    · exact tw0_0_3_7_calc_x j
    · exact tw0_0_3_8_calc_x j
    · exact tw0_0_3_9_calc_x j
    · exact tw0_0_3_10_calc_x j
    · exact tw0_0_3_11_calc_x j
    · exact tw0_0_3_12_calc_x j
    · exact tw0_0_3_13_calc_x j
    · exact tw0_0_3_14_calc_x j
    · exact tw0_0_3_15_calc_x j
    · exact tw0_0_3_16_calc j
    · exact tw0_0_3_17_calc j
    · exact tw0_0_3_18_calc j
    · exact tw0_0_3_19_calc j
    · exact tw0_0_3_20_calc j
  rw [← he]
  exact taylorWaveBox_mem_x 0 0 3 l j

end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorWave00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma tw0_0_mem (n : Fin 7) (l : Fin 21) (j : Fin 31) : (tw0_0 n l j).Mem (taylorWave 0 0 (nearNode n) l.val (frequency j)) := by
  fin_cases n
  · exact tw0_0_0_mem_x l j
  · exact tw0_0_1_mem_x l j
  · exact tw0_0_2_mem_x l j
  · exact tw0_0_3_mem l j
  · exact tw0_0_4_mem_x l j
  · exact tw0_0_5_mem_x l j
  · exact tw0_0_6_mem_x l j
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRowsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma taylorWaveTable_mem (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveTable q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact tw0_0_mem n l j
  · exact tw0_1_mem_x n l j
  · exact tw1_0_mem_x n l j
  · exact tw1_1_mem_x n l j

lemma nearDisplacementBox_mem (n : Fin 7) (y : Fin 2) :
    (nearDisplacementBox n y).Mem (nearDisplacement n y) := by
  exact RI.mem_divNat (RI.mem_point _) (by norm_num)
lemma taylorRowBox_mem_x_oai (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) :
    (taylorRowBox side n y l r).Mem
      (taylorRow side (nearNode n) (nearDisplacement n y) l.val r) := by
  exact RI.mem_mul (RI.mem_pow (nearDisplacementBox_mem n y) l.val)
    (CI.mem_sum (fun q => CI.mem_sum (fun j => CI.mem_add
      (CI.mem_mul (spectrumTable_mem_x side q j r) (taylorWaveTable_mem q 0 n l j))
      (CI.mem_mul (spectrumTable_mem_x (otherSide side) q j r) (taylorWaveTable_mem q 1 n l j))))).1

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_x_oai
