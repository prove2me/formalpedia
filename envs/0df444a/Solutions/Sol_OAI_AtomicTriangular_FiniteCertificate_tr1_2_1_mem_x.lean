-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:49:14.563035+00:00
-- url     : https://prove2.me/submissions/00730e26-5ffd-430e-a729-43310088fdf6

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_7_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_2_1_8_calc (r : Fin 8) : taylorRowBox 1 2 1 8 r = tr1_2_1_8 r := by
  revert r
  decide +kernel
lemma tr1_2_1_9_calc (r : Fin 8) : taylorRowBox 1 2 1 9 r = tr1_2_1_9 r := by
  revert r
  decide +kernel
lemma tr1_2_1_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr1_2_1 l r).Mem (taylorRow 1 (nearNode 2) (nearDisplacement 2 1) l.val r) := by
  have he : taylorRowBox 1 2 1 l r = tr1_2_1 l r := by
    fin_cases l
    · exact tr1_2_1_0_calc_x r
    · exact tr1_2_1_1_calc_x r
    · exact tr1_2_1_2_calc_x r
    · exact tr1_2_1_3_calc_x r
    · exact tr1_2_1_4_calc_x r
    · exact tr1_2_1_5_calc_x r
    · exact tr1_2_1_6_calc_x r
    · exact tr1_2_1_7_calc_x r
    · exact tr1_2_1_8_calc r
    · exact tr1_2_1_9_calc r
    · exact tr1_2_1_10_calc_x r
    · exact tr1_2_1_11_calc_x r
    · exact tr1_2_1_12_calc_x r
    · exact tr1_2_1_13_calc_x r
    · exact tr1_2_1_14_calc_x r
    · exact tr1_2_1_15_calc_x r
    · exact tr1_2_1_16_calc_x r
    · exact tr1_2_1_17_calc_x r
    · exact tr1_2_1_18_calc_x r
    · exact tr1_2_1_19_calc_x r
    · exact tr1_2_1_20_calc_x r
  rw [← he]
  exact taylorRowBox_mem_x 1 2 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x_oai
