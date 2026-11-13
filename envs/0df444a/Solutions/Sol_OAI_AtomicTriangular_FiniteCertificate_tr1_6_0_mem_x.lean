-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:14:32.46981+00:00
-- url     : https://prove2.me/submissions/bd4eeb77-8f50-4e5f-a34f-1cddc87907f7

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_0_14_calc (r : Fin 8) : taylorRowBox 1 6 0 14 r = tr1_6_0_14 r := by
  revert r
  decide +kernel
lemma tr1_6_0_19_calc (r : Fin 8) : taylorRowBox 1 6 0 19 r = tr1_6_0_19 r := by
  revert r
  decide +kernel
lemma tr1_6_0_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr1_6_0 l r).Mem (taylorRow 1 (nearNode 6) (nearDisplacement 6 0) l.val r) := by
  have he : taylorRowBox 1 6 0 l r = tr1_6_0 l r := by
    fin_cases l
    · exact tr1_6_0_0_calc_x r
    · exact tr1_6_0_1_calc_x r
    · exact tr1_6_0_2_calc_x r
    · exact tr1_6_0_3_calc_x r
    · exact tr1_6_0_4_calc_x r
    · exact tr1_6_0_5_calc_x r
    · exact tr1_6_0_6_calc_x r
    · exact tr1_6_0_7_calc_x r
    · exact tr1_6_0_8_calc_x r
    · exact tr1_6_0_9_calc_x r
    · exact tr1_6_0_10_calc_x r
    · exact tr1_6_0_11_calc_x r
    · exact tr1_6_0_12_calc_x r
    · exact tr1_6_0_13_calc_x r
    · exact tr1_6_0_14_calc r
    · exact tr1_6_0_15_calc_x r
    · exact tr1_6_0_16_calc_x r
    · exact tr1_6_0_17_calc_x r
    · exact tr1_6_0_18_calc_x r
    · exact tr1_6_0_19_calc r
    · exact tr1_6_0_20_calc_x r
  rw [← he]
  exact taylorRowBox_mem_x 1 6 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_x_oai
