-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:49:48.515373+00:00
-- url     : https://prove2.me/submissions/56fee77e-684a-435a-b292-724e451193d3

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_1_1_18_calc (r : Fin 8) : taylorRowBox 1 1 1 18 r = tr1_1_1_18 r := by
  revert r
  decide +kernel
lemma tr1_1_1_20_calc (r : Fin 8) : taylorRowBox 1 1 1 20 r = tr1_1_1_20 r := by
  revert r
  decide +kernel
lemma tr1_1_1_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_1_1 l r).Mem (taylorRow 1 (nearNode 1) (nearDisplacement 1 1) l.val r) := by
  have he : taylorRowBox 1 1 1 l r = tr1_1_1 l r := by
    fin_cases l
    · exact tr1_1_1_0_calc_eu r
    · exact tr1_1_1_1_calc_eu r
    · exact tr1_1_1_2_calc_eu r
    · exact tr1_1_1_3_calc_eu r
    · exact tr1_1_1_4_calc_eu r
    · exact tr1_1_1_5_calc_eu r
    · exact tr1_1_1_6_calc_eu r
    · exact tr1_1_1_7_calc_eu r
    · exact tr1_1_1_8_calc_eu r
    · exact tr1_1_1_9_calc_eu r
    · exact tr1_1_1_10_calc_eu r
    · exact tr1_1_1_11_calc_eu r
    · exact tr1_1_1_12_calc_eu r
    · exact tr1_1_1_13_calc_eu r
    · exact tr1_1_1_14_calc_eu r
    · exact tr1_1_1_15_calc_eu r
    · exact tr1_1_1_16_calc_eu r
    · exact tr1_1_1_17_calc_eu r
    · exact tr1_1_1_18_calc r
    · exact tr1_1_1_19_calc_eu r
    · exact tr1_1_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem_eu 1 1 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_eu_oai
