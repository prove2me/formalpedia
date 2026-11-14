-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_0_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:48:20.794466+00:00
-- url     : https://prove2.me/submissions/e579a097-ca03-427b-8bb3-a4514de230b7

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_1_7_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_0_1_8_calc (r : Fin 8) : taylorRowBox 1 0 1 8 r = tr1_0_1_8 r := by
  revert r
  decide +kernel
lemma tr1_0_1_9_calc (r : Fin 8) : taylorRowBox 1 0 1 9 r = tr1_0_1_9 r := by
  revert r
  decide +kernel
lemma tr1_0_1_17_calc (r : Fin 8) : taylorRowBox 1 0 1 17 r = tr1_0_1_17 r := by
  revert r
  decide +kernel
lemma tr1_0_1_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_0_1 l r).Mem (taylorRow 1 (nearNode 0) (nearDisplacement 0 1) l.val r) := by
  have he : taylorRowBox 1 0 1 l r = tr1_0_1 l r := by
    fin_cases l
    · exact tr1_0_1_0_calc_eu r
    · exact tr1_0_1_1_calc_eu r
    · exact tr1_0_1_2_calc_eu r
    · exact tr1_0_1_3_calc_eu r
    · exact tr1_0_1_4_calc_eu r
    · exact tr1_0_1_5_calc_eu r
    · exact tr1_0_1_6_calc_eu r
    · exact tr1_0_1_7_calc_eu r
    · exact tr1_0_1_8_calc r
    · exact tr1_0_1_9_calc r
    · exact tr1_0_1_10_calc_eu r
    · exact tr1_0_1_11_calc_eu r
    · exact tr1_0_1_12_calc_eu r
    · exact tr1_0_1_13_calc_eu r
    · exact tr1_0_1_14_calc_eu r
    · exact tr1_0_1_15_calc_eu r
    · exact tr1_0_1_16_calc_eu r
    · exact tr1_0_1_17_calc r
    · exact tr1_0_1_18_calc_eu r
    · exact tr1_0_1_19_calc_eu r
    · exact tr1_0_1_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 0 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_0_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_0_1_mem_eu_oai
