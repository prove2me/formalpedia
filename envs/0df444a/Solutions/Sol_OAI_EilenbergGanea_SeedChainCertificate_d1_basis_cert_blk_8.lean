-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:36:47.090977+00:00
-- url     : https://prove2.me/submissions/7df63abc-7d9e-4292-a84c-7b9de6a169e0

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

theorem d1_basis_cert_80 : ∀ e : Fin 372,
    rowEval (d1Row 80) (fun j => if j = e then 1 else 0) =
      (if 80 = (edge e).2 then 1 else 0) -
      (if 80 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_81 : ∀ e : Fin 372,
    rowEval (d1Row 81) (fun j => if j = e then 1 else 0) =
      (if 81 = (edge e).2 then 1 else 0) -
      (if 81 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_82 : ∀ e : Fin 372,
    rowEval (d1Row 82) (fun j => if j = e then 1 else 0) =
      (if 82 = (edge e).2 then 1 else 0) -
      (if 82 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_83 : ∀ e : Fin 372,
    rowEval (d1Row 83) (fun j => if j = e then 1 else 0) =
      (if 83 = (edge e).2 then 1 else 0) -
      (if 83 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_84 : ∀ e : Fin 372,
    rowEval (d1Row 84) (fun j => if j = e then 1 else 0) =
      (if 84 = (edge e).2 then 1 else 0) -
      (if 84 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_85 : ∀ e : Fin 372,
    rowEval (d1Row 85) (fun j => if j = e then 1 else 0) =
      (if 85 = (edge e).2 then 1 else 0) -
      (if 85 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_86 : ∀ e : Fin 372,
    rowEval (d1Row 86) (fun j => if j = e then 1 else 0) =
      (if 86 = (edge e).2 then 1 else 0) -
      (if 86 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_87 : ∀ e : Fin 372,
    rowEval (d1Row 87) (fun j => if j = e then 1 else 0) =
      (if 87 = (edge e).2 then 1 else 0) -
      (if 87 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_88 : ∀ e : Fin 372,
    rowEval (d1Row 88) (fun j => if j = e then 1 else 0) =
      (if 88 = (edge e).2 then 1 else 0) -
      (if 88 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_89 : ∀ e : Fin 372,
    rowEval (d1Row 89) (fun j => if j = e then 1 else 0) =
      (if 89 = (edge e).2 then 1 else 0) -
      (if 89 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_8_oai (i : Fin 103) (hb : 80 ≤ i.val ∧ i.val < 90) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_80 e
  · exact d1_basis_cert_81 e
  · exact d1_basis_cert_82 e
  · exact d1_basis_cert_83 e
  · exact d1_basis_cert_84 e
  · exact d1_basis_cert_85 e
  · exact d1_basis_cert_86 e
  · exact d1_basis_cert_87 e
  · exact d1_basis_cert_88 e
  · exact d1_basis_cert_89 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_8_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_8_oai
