-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:19.470724+00:00
-- url     : https://prove2.me/submissions/f3030d50-425e-4d4a-a6c0-776061d27b82

import Mathlib
import Definitions.Def_OAIEGC000
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_0
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_1
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_10
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_2
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_3
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_4
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_5
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_6
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_7
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_8
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d1_basis_cert_blk_9

section
-- module Solutions.OAIEG.SeedContraction
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem d1_basis_cert_oai (i : Fin 103) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  have hlt := i.isLt
  rcases (by omega : (0 ≤ i.val ∧ i.val < 10) ∨ (10 ≤ i.val ∧ i.val < 20) ∨ (20 ≤ i.val ∧ i.val < 30) ∨ (30 ≤ i.val ∧ i.val < 40) ∨ (40 ≤ i.val ∧ i.val < 50) ∨ (50 ≤ i.val ∧ i.val < 60) ∨ (60 ≤ i.val ∧ i.val < 70) ∨ (70 ≤ i.val ∧ i.val < 80) ∨ (80 ≤ i.val ∧ i.val < 90) ∨ (90 ≤ i.val ∧ i.val < 100) ∨ (100 ≤ i.val ∧ i.val < 103)) with h | h | h | h | h | h | h | h | h | h | h
  · exact d1_basis_cert_blk_0 i h e
  · exact d1_basis_cert_blk_1 i h e
  · exact d1_basis_cert_blk_2 i h e
  · exact d1_basis_cert_blk_3 i h e
  · exact d1_basis_cert_blk_4 i h e
  · exact d1_basis_cert_blk_5 i h e
  · exact d1_basis_cert_blk_6 i h e
  · exact d1_basis_cert_blk_7 i h e
  · exact d1_basis_cert_blk_8 i h e
  · exact d1_basis_cert_blk_9 i h e
  · exact d1_basis_cert_blk_10 i h e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_oai
