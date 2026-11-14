-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:48:17.652759+00:00
-- url     : https://prove2.me/submissions/a3ba6830-a20c-491b-8b33-730ebede6346

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_8_calc_eu

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

lemma tr1_0_0_9_calc (r : Fin 8) : taylorRowBox 1 0 0 9 r = tr1_0_0_9 r := by
  revert r
  decide +kernel
lemma tr1_0_0_17_calc (r : Fin 8) : taylorRowBox 1 0 0 17 r = tr1_0_0_17 r := by
  revert r
  decide +kernel
lemma tr1_0_0_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_0_0 l r).Mem (taylorRow 1 (nearNode 0) (nearDisplacement 0 0) l.val r) := by
  have he : taylorRowBox 1 0 0 l r = tr1_0_0 l r := by
    fin_cases l
    · exact tr1_0_0_0_calc_eu r
    · exact tr1_0_0_1_calc_eu r
    · exact tr1_0_0_2_calc_eu r
    · exact tr1_0_0_3_calc_eu r
    · exact tr1_0_0_4_calc_eu r
    · exact tr1_0_0_5_calc_eu r
    · exact tr1_0_0_6_calc_eu r
    · exact tr1_0_0_7_calc_eu r
    · exact tr1_0_0_8_calc_eu r
    · exact tr1_0_0_9_calc r
    · exact tr1_0_0_10_calc_eu r
    · exact tr1_0_0_11_calc_eu r
    · exact tr1_0_0_12_calc_eu r
    · exact tr1_0_0_13_calc_eu r
    · exact tr1_0_0_14_calc_eu r
    · exact tr1_0_0_15_calc_eu r
    · exact tr1_0_0_16_calc_eu r
    · exact tr1_0_0_17_calc r
    · exact tr1_0_0_18_calc_eu r
    · exact tr1_0_0_19_calc_eu r
    · exact tr1_0_0_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 0 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_eu_oai
