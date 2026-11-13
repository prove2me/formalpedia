-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:31:41.169554+00:00
-- url     : https://prove2.me/submissions/b2b45598-b8b1-48cc-b68e-e95dbb213304

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_6_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_6_1_16_calc (r : Fin 8) : taylorRowBox 0 6 1 16 r = tr0_6_1_16 r := by
  revert r
  decide +kernel
lemma tr0_6_1_17_calc (r : Fin 8) : taylorRowBox 0 6 1 17 r = tr0_6_1_17 r := by
  revert r
  decide +kernel
lemma tr0_6_1_18_calc (r : Fin 8) : taylorRowBox 0 6 1 18 r = tr0_6_1_18 r := by
  revert r
  decide +kernel
lemma tr0_6_1_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr0_6_1 l r).Mem (taylorRow 0 (nearNode 6) (nearDisplacement 6 1) l.val r) := by
  have he : taylorRowBox 0 6 1 l r = tr0_6_1 l r := by
    fin_cases l
    · exact tr0_6_1_0_calc_x r
    · exact tr0_6_1_1_calc_x r
    · exact tr0_6_1_2_calc_x r
    · exact tr0_6_1_3_calc_x r
    · exact tr0_6_1_4_calc_x r
    · exact tr0_6_1_5_calc_x r
    · exact tr0_6_1_6_calc_x r
    · exact tr0_6_1_7_calc_x r
    · exact tr0_6_1_8_calc_x r
    · exact tr0_6_1_9_calc_x r
    · exact tr0_6_1_10_calc_x r
    · exact tr0_6_1_11_calc_x r
    · exact tr0_6_1_12_calc_x r
    · exact tr0_6_1_13_calc_x r
    · exact tr0_6_1_14_calc_x r
    · exact tr0_6_1_15_calc_x r
    · exact tr0_6_1_16_calc r
    · exact tr0_6_1_17_calc r
    · exact tr0_6_1_18_calc r
    · exact tr0_6_1_19_calc_x r
    · exact tr0_6_1_20_calc_x r
  rw [← he]
  exact taylorRowBox_mem_x 0 6 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_mem_x_oai
