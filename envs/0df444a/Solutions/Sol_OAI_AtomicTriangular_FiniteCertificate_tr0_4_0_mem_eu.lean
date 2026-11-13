-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_mem_eu
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:08:34.093059+00:00
-- url     : https://prove2.me/submissions/c378b398-1e32-4b55-a827-6afcb670cb19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_4_0_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_4_0_19_calc (r : Fin 8) : taylorRowBox 0 4 0 19 r = tr0_4_0_19 r := by
  revert r
  decide +kernel
lemma tr0_4_0_20_calc (r : Fin 8) : taylorRowBox 0 4 0 20 r = tr0_4_0_20 r := by
  revert r
  decide +kernel
lemma tr0_4_0_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr0_4_0 l r).Mem (taylorRow 0 (nearNode 4) (nearDisplacement 4 0) l.val r) := by
  have he : taylorRowBox 0 4 0 l r = tr0_4_0 l r := by
    fin_cases l
    · exact tr0_4_0_0_calc_eu r
    · exact tr0_4_0_1_calc_eu r
    · exact tr0_4_0_2_calc_eu r
    · exact tr0_4_0_3_calc_eu r
    · exact tr0_4_0_4_calc_eu r
    · exact tr0_4_0_5_calc_eu r
    · exact tr0_4_0_6_calc_eu r
    · exact tr0_4_0_7_calc_eu r
    · exact tr0_4_0_8_calc_eu r
    · exact tr0_4_0_9_calc_eu r
    · exact tr0_4_0_10_calc_eu r
    · exact tr0_4_0_11_calc_eu r
    · exact tr0_4_0_12_calc_eu r
    · exact tr0_4_0_13_calc_eu r
    · exact tr0_4_0_14_calc_eu r
    · exact tr0_4_0_15_calc_eu r
    · exact tr0_4_0_16_calc_eu r
    · exact tr0_4_0_17_calc_eu r
    · exact tr0_4_0_18_calc_eu r
    · exact tr0_4_0_19_calc r
    · exact tr0_4_0_20_calc r
  rw [← he]
  exact taylorRowBox_mem_eu 0 4 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_mem_eu_oai
