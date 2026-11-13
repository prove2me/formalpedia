-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_mem_eu
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:50:46.422206+00:00
-- url     : https://prove2.me/submissions/7115303a-250d-4fb5-8940-292f1363ce8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_19_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_20_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_3_0_9_calc_eu

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

lemma tr1_3_0_0_calc (r : Fin 8) : taylorRowBox 1 3 0 0 r = tr1_3_0_0 r := by
  revert r
  decide +kernel
lemma tr1_3_0_10_calc (r : Fin 8) : taylorRowBox 1 3 0 10 r = tr1_3_0_10 r := by
  revert r
  decide +kernel
lemma tr1_3_0_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr1_3_0 l r).Mem (taylorRow 1 (nearNode 3) (nearDisplacement 3 0) l.val r) := by
  have he : taylorRowBox 1 3 0 l r = tr1_3_0 l r := by
    fin_cases l
    · exact tr1_3_0_0_calc r
    · exact tr1_3_0_1_calc_eu r
    · exact tr1_3_0_2_calc_eu r
    · exact tr1_3_0_3_calc_eu r
    · exact tr1_3_0_4_calc_eu r
    · exact tr1_3_0_5_calc_eu r
    · exact tr1_3_0_6_calc_eu r
    · exact tr1_3_0_7_calc_eu r
    · exact tr1_3_0_8_calc_eu r
    · exact tr1_3_0_9_calc_eu r
    · exact tr1_3_0_10_calc r
    · exact tr1_3_0_11_calc_eu r
    · exact tr1_3_0_12_calc_eu r
    · exact tr1_3_0_13_calc_eu r
    · exact tr1_3_0_14_calc_eu r
    · exact tr1_3_0_15_calc_eu r
    · exact tr1_3_0_16_calc_eu r
    · exact tr1_3_0_17_calc_eu r
    · exact tr1_3_0_18_calc_eu r
    · exact tr1_3_0_19_calc_eu r
    · exact tr1_3_0_20_calc_eu r
  rw [← he]
  exact taylorRowBox_mem_eu 1 3 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_mem_eu_oai
