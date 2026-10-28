-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:37:52.382109+00:00
-- url     : https://prove2.me/submissions/15def08b-9faa-41aa-a259-8529727e0ca0

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

theorem d1_basis_cert_90 : ∀ e : Fin 372,
    rowEval (d1Row 90) (fun j => if j = e then 1 else 0) =
      (if 90 = (edge e).2 then 1 else 0) -
      (if 90 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_91 : ∀ e : Fin 372,
    rowEval (d1Row 91) (fun j => if j = e then 1 else 0) =
      (if 91 = (edge e).2 then 1 else 0) -
      (if 91 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_92 : ∀ e : Fin 372,
    rowEval (d1Row 92) (fun j => if j = e then 1 else 0) =
      (if 92 = (edge e).2 then 1 else 0) -
      (if 92 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_93 : ∀ e : Fin 372,
    rowEval (d1Row 93) (fun j => if j = e then 1 else 0) =
      (if 93 = (edge e).2 then 1 else 0) -
      (if 93 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_94 : ∀ e : Fin 372,
    rowEval (d1Row 94) (fun j => if j = e then 1 else 0) =
      (if 94 = (edge e).2 then 1 else 0) -
      (if 94 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_95 : ∀ e : Fin 372,
    rowEval (d1Row 95) (fun j => if j = e then 1 else 0) =
      (if 95 = (edge e).2 then 1 else 0) -
      (if 95 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_96 : ∀ e : Fin 372,
    rowEval (d1Row 96) (fun j => if j = e then 1 else 0) =
      (if 96 = (edge e).2 then 1 else 0) -
      (if 96 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_97 : ∀ e : Fin 372,
    rowEval (d1Row 97) (fun j => if j = e then 1 else 0) =
      (if 97 = (edge e).2 then 1 else 0) -
      (if 97 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_98 : ∀ e : Fin 372,
    rowEval (d1Row 98) (fun j => if j = e then 1 else 0) =
      (if 98 = (edge e).2 then 1 else 0) -
      (if 98 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_99 : ∀ e : Fin 372,
    rowEval (d1Row 99) (fun j => if j = e then 1 else 0) =
      (if 99 = (edge e).2 then 1 else 0) -
      (if 99 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_9_oai (i : Fin 103) (hb : 90 ≤ i.val ∧ i.val < 100) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_90 e
  · exact d1_basis_cert_91 e
  · exact d1_basis_cert_92 e
  · exact d1_basis_cert_93 e
  · exact d1_basis_cert_94 e
  · exact d1_basis_cert_95 e
  · exact d1_basis_cert_96 e
  · exact d1_basis_cert_97 e
  · exact d1_basis_cert_98 e
  · exact d1_basis_cert_99 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_9_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_9_oai
