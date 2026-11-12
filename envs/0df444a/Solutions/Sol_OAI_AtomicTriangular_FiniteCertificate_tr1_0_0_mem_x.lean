-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_x
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:36:24.0442+00:00
-- url     : https://prove2.me/submissions/6df03f75-30b0-4dd3-9479-0b0553dfcd46
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_18_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_19_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_20_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_0_0_8_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows10
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
lemma tr1_0_0_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr1_0_0 l r).Mem (taylorRow 1 (nearNode 0) (nearDisplacement 0 0) l.val r) := by
  have he : taylorRowBox 1 0 0 l r = tr1_0_0 l r := by
    fin_cases l
    · exact tr1_0_0_0_calc_x r
    · exact tr1_0_0_1_calc_x r
    · exact tr1_0_0_2_calc_x r
    · exact tr1_0_0_3_calc_x r
    · exact tr1_0_0_4_calc_x r
    · exact tr1_0_0_5_calc_x r
    · exact tr1_0_0_6_calc_x r
    · exact tr1_0_0_7_calc_x r
    · exact tr1_0_0_8_calc_x r
    · exact tr1_0_0_9_calc r
    · exact tr1_0_0_10_calc_x r
    · exact tr1_0_0_11_calc_x r
    · exact tr1_0_0_12_calc_x r
    · exact tr1_0_0_13_calc_x r
    · exact tr1_0_0_14_calc_x r
    · exact tr1_0_0_15_calc_x r
    · exact tr1_0_0_16_calc_x r
    · exact tr1_0_0_17_calc r
    · exact tr1_0_0_18_calc_x r
    · exact tr1_0_0_19_calc_x r
    · exact tr1_0_0_20_calc_x r
  rw [← he]
  exact taylorRowBox_mem_x 1 0 0 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_x_oai
