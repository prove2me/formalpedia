-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_mem_x
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:20:31.248254+00:00
-- url     : https://prove2.me/submissions/58dae9e1-3931-4c2b-87ac-b7ab649133c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr0_5_0_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

lemma tr0_5_0_19_calc (r : Fin 8) : taylorRowBox 0 5 0 19 r = tr0_5_0_19 r := by
  revert r
  decide +kernel
lemma tr0_5_0_20_calc (r : Fin 8) : taylorRowBox 0 5 0 20 r = tr0_5_0_20 r := by
  revert r
  decide +kernel
lemma tr0_5_0_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr0_5_0 l r).Mem (taylorRow 0 (nearNode 5) (nearDisplacement 5 0) l.val r) := by
  have he : taylorRowBox 0 5 0 l r = tr0_5_0 l r := by
    fin_cases l
    · exact tr0_5_0_0_calc_x r
    · exact tr0_5_0_1_calc_x r
    · exact tr0_5_0_2_calc_x r
    · exact tr0_5_0_3_calc_x r
    · exact tr0_5_0_4_calc_x r
    · exact tr0_5_0_5_calc_x r
    · exact tr0_5_0_6_calc_x r
    · exact tr0_5_0_7_calc_x r
    · exact tr0_5_0_8_calc_x r
    · exact tr0_5_0_9_calc_x r
    · exact tr0_5_0_10_calc_x r
    · exact tr0_5_0_11_calc_x r
    · exact tr0_5_0_12_calc_x r
    · exact tr0_5_0_13_calc_x r
    · exact tr0_5_0_14_calc_x r
    · exact tr0_5_0_15_calc_x r
    · exact tr0_5_0_16_calc_x r
    · exact tr0_5_0_17_calc_x r
    · exact tr0_5_0_18_calc_x r
    · exact tr0_5_0_19_calc r
    · exact tr0_5_0_20_calc r
  rw [← he]
  exact taylorRowBox_mem_x 0 5 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_mem_x_oai
