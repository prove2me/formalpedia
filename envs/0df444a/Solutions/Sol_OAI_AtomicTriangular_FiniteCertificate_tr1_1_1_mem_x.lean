-- Prove2me | solution 1 for OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_x
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:44:54.867206+00:00
-- url     : https://prove2.me/submissions/26a6a487-55bb-410b-93d8-b416910f2433
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ257X023
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_0_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_10_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_11_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_12_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_13_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_14_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_15_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_16_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_17_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_1_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_2_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_3_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_4_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_5_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_6_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_7_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_8_calc_x
import Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_1_1_9_calc_x

section
-- module Solutions.OAIQ250_TR.Triangular_Taylor_TaylorRows11
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
lemma tr1_1_1_19_calc (r : Fin 8) : taylorRowBox 1 1 1 19 r = tr1_1_1_19 r := by
  revert r
  decide +kernel
lemma tr1_1_1_20_calc (r : Fin 8) : taylorRowBox 1 1 1 20 r = tr1_1_1_20 r := by
  revert r
  decide +kernel
lemma tr1_1_1_mem_x_oai (l : Fin 21) (r : Fin 8) : (tr1_1_1 l r).Mem (taylorRow 1 (nearNode 1) (nearDisplacement 1 1) l.val r) := by
  have he : taylorRowBox 1 1 1 l r = tr1_1_1 l r := by
    fin_cases l
    · exact tr1_1_1_0_calc_x r
    · exact tr1_1_1_1_calc_x r
    · exact tr1_1_1_2_calc_x r
    · exact tr1_1_1_3_calc_x r
    · exact tr1_1_1_4_calc_x r
    · exact tr1_1_1_5_calc_x r
    · exact tr1_1_1_6_calc_x r
    · exact tr1_1_1_7_calc_x r
    · exact tr1_1_1_8_calc_x r
    · exact tr1_1_1_9_calc_x r
    · exact tr1_1_1_10_calc_x r
    · exact tr1_1_1_11_calc_x r
    · exact tr1_1_1_12_calc_x r
    · exact tr1_1_1_13_calc_x r
    · exact tr1_1_1_14_calc_x r
    · exact tr1_1_1_15_calc_x r
    · exact tr1_1_1_16_calc_x r
    · exact tr1_1_1_17_calc_x r
    · exact tr1_1_1_18_calc r
    · exact tr1_1_1_19_calc r
    · exact tr1_1_1_20_calc r
  rw [← he]
  exact taylorRowBox_mem_x 1 1 1 l r
end AtomicTriangular.FiniteCertificate
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_x_oai := @OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_x_oai
