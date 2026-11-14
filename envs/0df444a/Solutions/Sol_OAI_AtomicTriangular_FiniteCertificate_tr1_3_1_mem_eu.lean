-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:51:15.511207+00:00
-- url     : https://prove2.me/submissions/4caa466e-ed83-4be1-832d-07ab5535284f

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_1_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_3_1_0_calc (r : Fin 8) : taylorRowBox 1 3 1 0 r = tr1_3_1_0 r := by
  revert r
  decide +kernel
lemma tr1_3_1_10_calc (r : Fin 8) : taylorRowBox 1 3 1 10 r = tr1_3_1_10 r := by
  revert r
  decide +kernel
lemma tr1_3_1_11_calc (r : Fin 8) : taylorRowBox 1 3 1 11 r = tr1_3_1_11 r := by
  revert r
  decide +kernel
lemma tr1_3_1_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_3_1 l r).Mem (taylorRow 1 (nearNode 3) (nearDisplacement 3 1) l.val r) := by
  have he : taylorRowBox 1 3 1 l r = tr1_3_1 l r := by
    fin_cases l
    · exact tr1_3_1_0_calc r
    · exact tr1_3_1_1_calc_eu r
    · exact tr1_3_1_2_calc_eu r
    · exact tr1_3_1_3_calc_eu r
    · exact tr1_3_1_4_calc_eu r
    · exact tr1_3_1_5_calc_eu r
    · exact tr1_3_1_6_calc_eu r
    · exact tr1_3_1_7_calc_eu r
    · exact tr1_3_1_8_calc_eu r
    · exact tr1_3_1_9_calc_eu r
    · exact tr1_3_1_10_calc r
    · exact tr1_3_1_11_calc r
    · exact tr1_3_1_12_calc_eu r
    · exact tr1_3_1_13_calc_eu r
    · exact tr1_3_1_14_calc_eu r
    · exact tr1_3_1_15_calc_eu r
    · exact tr1_3_1_16_calc_eu r
    · exact tr1_3_1_17_calc_eu r
    · exact tr1_3_1_18_calc_eu r
    · exact tr1_3_1_19_calc_eu r
    · exact tr1_3_1_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 3 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_mem_eu_oai
