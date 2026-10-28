-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:30:53.682485+00:00
-- url     : https://prove2.me/submissions/93d3a77f-ef7c-4eed-b220-fa8b5f3dff9e

import Mathlib
import Definitions.Def_OAIEGC000

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

theorem d1_basis_cert_100 : ∀ e : Fin 372,
    rowEval (d1Row 100) (fun j => if j = e then 1 else 0) =
      (if 100 = (edge e).2 then 1 else 0) -
      (if 100 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_101 : ∀ e : Fin 372,
    rowEval (d1Row 101) (fun j => if j = e then 1 else 0) =
      (if 101 = (edge e).2 then 1 else 0) -
      (if 101 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_102 : ∀ e : Fin 372,
    rowEval (d1Row 102) (fun j => if j = e then 1 else 0) =
      (if 102 = (edge e).2 then 1 else 0) -
      (if 102 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_10_oai (i : Fin 103) (hb : 100 ≤ i.val ∧ i.val < 103) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_100 e
  · exact d1_basis_cert_101 e
  · exact d1_basis_cert_102 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_10_oai
