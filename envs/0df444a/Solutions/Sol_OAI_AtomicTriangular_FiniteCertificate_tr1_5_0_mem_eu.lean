-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_mem_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:19:57.191319+00:00
-- url     : https://prove2.me/submissions/9c2a0954-f88d-4089-83d2-0c7967bef474

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_5_0_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_5_0_16_calc (r : Fin 8) : taylorRowBox 1 5 0 16 r = tr1_5_0_16 r := by
  revert r
  decide +kernel
lemma tr1_5_0_17_calc (r : Fin 8) : taylorRowBox 1 5 0 17 r = tr1_5_0_17 r := by
  revert r
  decide +kernel
lemma tr1_5_0_18_calc (r : Fin 8) : taylorRowBox 1 5 0 18 r = tr1_5_0_18 r := by
  revert r
  decide +kernel
lemma tr1_5_0_19_calc (r : Fin 8) : taylorRowBox 1 5 0 19 r = tr1_5_0_19 r := by
  revert r
  decide +kernel
lemma tr1_5_0_20_calc (r : Fin 8) : taylorRowBox 1 5 0 20 r = tr1_5_0_20 r := by
  revert r
  decide +kernel
lemma tr1_5_0_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_5_0 l r).Mem (taylorRow 1 (nearNode 5) (nearDisplacement 5 0) l.val r) := by
  have he : taylorRowBox 1 5 0 l r = tr1_5_0 l r := by
    fin_cases l
    · exact tr1_5_0_0_calc_eu r
    · exact tr1_5_0_1_calc_eu r
    · exact tr1_5_0_2_calc_eu r
    · exact tr1_5_0_3_calc_eu r
    · exact tr1_5_0_4_calc_eu r
    · exact tr1_5_0_5_calc_eu r
    · exact tr1_5_0_6_calc_eu r
    · exact tr1_5_0_7_calc_eu r
    · exact tr1_5_0_8_calc_eu r
    · exact tr1_5_0_9_calc_eu r
    · exact tr1_5_0_10_calc_eu r
    · exact tr1_5_0_11_calc_eu r
    · exact tr1_5_0_12_calc_eu r
    · exact tr1_5_0_13_calc_eu r
    · exact tr1_5_0_14_calc_eu r
    · exact tr1_5_0_15_calc_eu r
    · exact tr1_5_0_16_calc r
    · exact tr1_5_0_17_calc r
    · exact tr1_5_0_18_calc r
    · exact tr1_5_0_19_calc r
    · exact tr1_5_0_20_calc r
  rw [← he]
  exact taylorRowBox_mem_eu 1 5 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_mem_eu_oai
