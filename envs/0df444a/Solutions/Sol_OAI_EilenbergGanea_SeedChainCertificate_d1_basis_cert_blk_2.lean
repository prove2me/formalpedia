-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:30:54.851665+00:00
-- url     : https://prove2.me/submissions/5b7afd7d-fa1a-49b6-97ad-b566ac7415d5

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

theorem d1_basis_cert_20 : ∀ e : Fin 372,
    rowEval (d1Row 20) (fun j => if j = e then 1 else 0) =
      (if 20 = (edge e).2 then 1 else 0) -
      (if 20 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_21 : ∀ e : Fin 372,
    rowEval (d1Row 21) (fun j => if j = e then 1 else 0) =
      (if 21 = (edge e).2 then 1 else 0) -
      (if 21 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_22 : ∀ e : Fin 372,
    rowEval (d1Row 22) (fun j => if j = e then 1 else 0) =
      (if 22 = (edge e).2 then 1 else 0) -
      (if 22 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_23 : ∀ e : Fin 372,
    rowEval (d1Row 23) (fun j => if j = e then 1 else 0) =
      (if 23 = (edge e).2 then 1 else 0) -
      (if 23 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_24 : ∀ e : Fin 372,
    rowEval (d1Row 24) (fun j => if j = e then 1 else 0) =
      (if 24 = (edge e).2 then 1 else 0) -
      (if 24 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_25 : ∀ e : Fin 372,
    rowEval (d1Row 25) (fun j => if j = e then 1 else 0) =
      (if 25 = (edge e).2 then 1 else 0) -
      (if 25 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_26 : ∀ e : Fin 372,
    rowEval (d1Row 26) (fun j => if j = e then 1 else 0) =
      (if 26 = (edge e).2 then 1 else 0) -
      (if 26 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_27 : ∀ e : Fin 372,
    rowEval (d1Row 27) (fun j => if j = e then 1 else 0) =
      (if 27 = (edge e).2 then 1 else 0) -
      (if 27 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_28 : ∀ e : Fin 372,
    rowEval (d1Row 28) (fun j => if j = e then 1 else 0) =
      (if 28 = (edge e).2 then 1 else 0) -
      (if 28 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_29 : ∀ e : Fin 372,
    rowEval (d1Row 29) (fun j => if j = e then 1 else 0) =
      (if 29 = (edge e).2 then 1 else 0) -
      (if 29 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_2_oai (i : Fin 103) (hb : 20 ≤ i.val ∧ i.val < 30) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_20 e
  · exact d1_basis_cert_21 e
  · exact d1_basis_cert_22 e
  · exact d1_basis_cert_23 e
  · exact d1_basis_cert_24 e
  · exact d1_basis_cert_25 e
  · exact d1_basis_cert_26 e
  · exact d1_basis_cert_27 e
  · exact d1_basis_cert_28 e
  · exact d1_basis_cert_29 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_2_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_2_oai
