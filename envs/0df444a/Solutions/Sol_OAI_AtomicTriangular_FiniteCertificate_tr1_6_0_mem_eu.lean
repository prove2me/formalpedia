-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_eu
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:52:46.770809+00:00
-- url     : https://prove2.me/submissions/da753868-2605-4da2-8e4d-ba3613cea07a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_6_0_9_calc_eu

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

lemma tr1_6_0_14_calc (r : Fin 8) : taylorRowBox 1 6 0 14 r = tr1_6_0_14 r := by
  revert r
  decide +kernel
lemma tr1_6_0_19_calc (r : Fin 8) : taylorRowBox 1 6 0 19 r = tr1_6_0_19 r := by
  revert r
  decide +kernel
lemma tr1_6_0_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_6_0 l r).Mem (taylorRow 1 (nearNode 6) (nearDisplacement 6 0) l.val r) := by
  have he : taylorRowBox 1 6 0 l r = tr1_6_0 l r := by
    fin_cases l
    · exact tr1_6_0_0_calc_eu r
    · exact tr1_6_0_1_calc_eu r
    · exact tr1_6_0_2_calc_eu r
    · exact tr1_6_0_3_calc_eu r
    · exact tr1_6_0_4_calc_eu r
    · exact tr1_6_0_5_calc_eu r
    · exact tr1_6_0_6_calc_eu r
    · exact tr1_6_0_7_calc_eu r
    · exact tr1_6_0_8_calc_eu r
    · exact tr1_6_0_9_calc_eu r
    · exact tr1_6_0_10_calc_eu r
    · exact tr1_6_0_11_calc_eu r
    · exact tr1_6_0_12_calc_eu r
    · exact tr1_6_0_13_calc_eu r
    · exact tr1_6_0_14_calc r
    · exact tr1_6_0_15_calc_eu r
    · exact tr1_6_0_16_calc_eu r
    · exact tr1_6_0_17_calc_eu r
    · exact tr1_6_0_18_calc_eu r
    · exact tr1_6_0_19_calc r
    · exact tr1_6_0_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 6 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_eu_oai
