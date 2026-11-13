-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_mem_eu
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:07:00.933312+00:00
-- url     : https://prove2.me/submissions/d95893a7-793d-4beb-b0b1-0e70908d35b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ334E023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_0_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_10_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_11_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_12_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_13_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_14_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_15_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_16_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_17_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_18_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_1_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_2_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_3_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_4_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_5_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_6_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_7_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_8_calc_eu
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_1_1_9_calc_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Taylor_TaylorRows01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_1_1_19_calc (r : Fin 8) : taylorRowBox 0 1 1 19 r = tr0_1_1_19 r := by
  revert r
  decide +kernel
lemma tr0_1_1_20_calc (r : Fin 8) : taylorRowBox 0 1 1 20 r = tr0_1_1_20 r := by
  revert r
  decide +kernel
lemma tr0_1_1_mem_eu_oai (l : Fin 21) (r : Fin 8) : (tr0_1_1 l r).Mem (taylorRow 0 (nearNode 1) (nearDisplacement 1 1) l.val r) := by
  have he : taylorRowBox 0 1 1 l r = tr0_1_1 l r := by
    fin_cases l
    · exact tr0_1_1_0_calc_eu r
    · exact tr0_1_1_1_calc_eu r
    · exact tr0_1_1_2_calc_eu r
    · exact tr0_1_1_3_calc_eu r
    · exact tr0_1_1_4_calc_eu r
    · exact tr0_1_1_5_calc_eu r
    · exact tr0_1_1_6_calc_eu r
    · exact tr0_1_1_7_calc_eu r
    · exact tr0_1_1_8_calc_eu r
    · exact tr0_1_1_9_calc_eu r
    · exact tr0_1_1_10_calc_eu r
    · exact tr0_1_1_11_calc_eu r
    · exact tr0_1_1_12_calc_eu r
    · exact tr0_1_1_13_calc_eu r
    · exact tr0_1_1_14_calc_eu r
    · exact tr0_1_1_15_calc_eu r
    · exact tr0_1_1_16_calc_eu r
    · exact tr0_1_1_17_calc_eu r
    · exact tr0_1_1_18_calc_eu r
    · exact tr0_1_1_19_calc r
    · exact tr0_1_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem_eu 0 1 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_mem_eu_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_mem_eu_oai
