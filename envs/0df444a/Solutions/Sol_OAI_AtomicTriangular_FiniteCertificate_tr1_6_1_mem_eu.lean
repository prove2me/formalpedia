-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_mem_eu
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:53:17.751047+00:00
-- url     : https://prove2.me/submissions/9ce63555-2d2f-4ad9-8a77-dadcf8f51393
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_1_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr1_6_1_17_calc (r : Fin 8) : taylorRowBox 1 6 1 17 r = tr1_6_1_17 r := by
  revert r
  decide +kernel
lemma tr1_6_1_19_calc (r : Fin 8) : taylorRowBox 1 6 1 19 r = tr1_6_1_19 r := by
  revert r
  decide +kernel
lemma tr1_6_1_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_6_1 l r).Mem (taylorRow 1 (nearNode 6) (nearDisplacement 6 1) l.val r) := by
  have he : taylorRowBox 1 6 1 l r = tr1_6_1 l r := by
    fin_cases l
    · exact tr1_6_1_0_calc_eu r
    · exact tr1_6_1_1_calc_eu r
    · exact tr1_6_1_2_calc_eu r
    · exact tr1_6_1_3_calc_eu r
    · exact tr1_6_1_4_calc_eu r
    · exact tr1_6_1_5_calc_eu r
    · exact tr1_6_1_6_calc_eu r
    · exact tr1_6_1_7_calc_eu r
    · exact tr1_6_1_8_calc_eu r
    · exact tr1_6_1_9_calc_eu r
    · exact tr1_6_1_10_calc_eu r
    · exact tr1_6_1_11_calc_eu r
    · exact tr1_6_1_12_calc_eu r
    · exact tr1_6_1_13_calc_eu r
    · exact tr1_6_1_14_calc_eu r
    · exact tr1_6_1_15_calc_eu r
    · exact tr1_6_1_16_calc_eu r
    · exact tr1_6_1_17_calc r
    · exact tr1_6_1_18_calc_eu r
    · exact tr1_6_1_19_calc r
    · exact tr1_6_1_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 6 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_mem_eu_oai
