-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:52:40.350613+00:00
-- url     : https://prove2.me/submissions/83a65b32-6ca1-453e-bbbf-8b07b73ab72f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_0_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_0_1_0_calc (r : Fin 8) : taylorRowBox 0 0 1 0 r = tr0_0_1_0 r := by
  revert r
  decide +kernel
lemma tr0_0_1_10_calc (r : Fin 8) : taylorRowBox 0 0 1 10 r = tr0_0_1_10 r := by
  revert r
  decide +kernel
lemma tr0_0_1_11_calc (r : Fin 8) : taylorRowBox 0 0 1 11 r = tr0_0_1_11 r := by
  revert r
  decide +kernel
lemma tr0_0_1_20_calc (r : Fin 8) : taylorRowBox 0 0 1 20 r = tr0_0_1_20 r := by
  revert r
  decide +kernel
lemma tr0_0_1_mem (l : Fin 21) (r : Fin 8) : (tr0_0_1 l r).Mem (taylorRow 0 (nearNode 0) (nearDisplacement 0 1) l.val r) := by
  have he : taylorRowBox 0 0 1 l r = tr0_0_1 l r := by
    fin_cases l
    · exact tr0_0_1_0_calc r
    · exact tr0_0_1_1_calc_x r
    · exact tr0_0_1_2_calc_x r
    · exact tr0_0_1_3_calc_x r
    · exact tr0_0_1_4_calc_x r
    · exact tr0_0_1_5_calc_x r
    · exact tr0_0_1_6_calc_x r
    · exact tr0_0_1_7_calc_x r
    · exact tr0_0_1_8_calc_x r
    · exact tr0_0_1_9_calc_x r
    · exact tr0_0_1_10_calc r
    · exact tr0_0_1_11_calc r
    · exact tr0_0_1_12_calc_x r
    · exact tr0_0_1_13_calc_x r
    · exact tr0_0_1_14_calc_x r
    · exact tr0_0_1_15_calc_x r
    · exact tr0_0_1_16_calc_x r
    · exact tr0_0_1_17_calc_x r
    · exact tr0_0_1_18_calc_x r
    · exact tr0_0_1_19_calc_x r
    · exact tr0_0_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem_x 0 0 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_ExceptionalInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma exceptional_tr_mem (l : Fin 21) (r : Fin 8) :
    (tr0_0_1 l r).Mem (taylorRow 0 1 1 l.val r) := by
  have hh := tr0_0_1_mem l r
  have hn : nearNode 0 = 1 := by norm_num [nearNode, finiteNode, residue]
  have hy : nearDisplacement 0 1 = 1 := by norm_num [nearDisplacement,nearDisplacementNum]
  simpa only [hn,hy] using hh
lemma ep0 : (RI.point 0).Mem (0 : ℝ) := by simpa using RI.mem_point 0
lemma frozenTaylorRowBox_mem_x_oai {z : RI} {x : ℝ} (hz : z.Mem x) (l : Fin 21) (r : Fin 8) :
    (frozenTaylorRowBox z l r).Mem (frozenTaylorRow x l.val r) := by
  unfold frozenTaylorRowBox frozenTaylorRow
  apply RI.mem_sub
  · split_ifs
    · exact ep0
    · exact RI.mem_neg (exceptional_tr_mem l r)
  · split_ifs
    · exact RI.mem_mul hz (exceptional_tr_mem l 0)
    · exact ep0

end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x_oai
