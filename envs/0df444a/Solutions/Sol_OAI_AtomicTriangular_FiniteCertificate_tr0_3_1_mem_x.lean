-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_mem_x
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:09:51.099254+00:00
-- url     : https://prove2.me/submissions/d4fff026-0de4-4e25-a06a-f58f241cafc5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_3_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_3_1_19_calc (r : Fin 8) : taylorRowBox 0 3 1 19 r = tr0_3_1_19 r := by
  revert r
  decide +kernel
lemma tr0_3_1_20_calc (r : Fin 8) : taylorRowBox 0 3 1 20 r = tr0_3_1_20 r := by
  revert r
  decide +kernel
lemma tr0_3_1_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr0_3_1 l r).Mem (taylorRow 0 (nearNode 3) (nearDisplacement 3 1) l.val r) := by
  have he : taylorRowBox 0 3 1 l r = tr0_3_1 l r := by
    fin_cases l
    · exact tr0_3_1_0_calc_x r
    · exact tr0_3_1_1_calc_x r
    · exact tr0_3_1_2_calc_x r
    · exact tr0_3_1_3_calc_x r
    · exact tr0_3_1_4_calc_x r
    · exact tr0_3_1_5_calc_x r
    · exact tr0_3_1_6_calc_x r
    · exact tr0_3_1_7_calc_x r
    · exact tr0_3_1_8_calc_x r
    · exact tr0_3_1_9_calc_x r
    · exact tr0_3_1_10_calc_x r
    · exact tr0_3_1_11_calc_x r
    · exact tr0_3_1_12_calc_x r
    · exact tr0_3_1_13_calc_x r
    · exact tr0_3_1_14_calc_x r
    · exact tr0_3_1_15_calc_x r
    · exact tr0_3_1_16_calc_x r
    · exact tr0_3_1_17_calc_x r
    · exact tr0_3_1_18_calc_x r
    · exact tr0_3_1_19_calc r
    · exact tr0_3_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem_x 0 3 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_mem_x_oai
