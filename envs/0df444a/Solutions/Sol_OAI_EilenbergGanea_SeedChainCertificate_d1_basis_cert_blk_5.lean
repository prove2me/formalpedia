-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:33:29.407988+00:00
-- url     : https://prove2.me/submissions/ff969e4c-e437-4f83-bca4-dc3dcb1782a2

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

theorem d1_basis_cert_50 : ∀ e : Fin 372,
    rowEval (d1Row 50) (fun j => if j = e then 1 else 0) =
      (if 50 = (edge e).2 then 1 else 0) -
      (if 50 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_51 : ∀ e : Fin 372,
    rowEval (d1Row 51) (fun j => if j = e then 1 else 0) =
      (if 51 = (edge e).2 then 1 else 0) -
      (if 51 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_52 : ∀ e : Fin 372,
    rowEval (d1Row 52) (fun j => if j = e then 1 else 0) =
      (if 52 = (edge e).2 then 1 else 0) -
      (if 52 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_53 : ∀ e : Fin 372,
    rowEval (d1Row 53) (fun j => if j = e then 1 else 0) =
      (if 53 = (edge e).2 then 1 else 0) -
      (if 53 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_54 : ∀ e : Fin 372,
    rowEval (d1Row 54) (fun j => if j = e then 1 else 0) =
      (if 54 = (edge e).2 then 1 else 0) -
      (if 54 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_55 : ∀ e : Fin 372,
    rowEval (d1Row 55) (fun j => if j = e then 1 else 0) =
      (if 55 = (edge e).2 then 1 else 0) -
      (if 55 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_56 : ∀ e : Fin 372,
    rowEval (d1Row 56) (fun j => if j = e then 1 else 0) =
      (if 56 = (edge e).2 then 1 else 0) -
      (if 56 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_57 : ∀ e : Fin 372,
    rowEval (d1Row 57) (fun j => if j = e then 1 else 0) =
      (if 57 = (edge e).2 then 1 else 0) -
      (if 57 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_58 : ∀ e : Fin 372,
    rowEval (d1Row 58) (fun j => if j = e then 1 else 0) =
      (if 58 = (edge e).2 then 1 else 0) -
      (if 58 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_59 : ∀ e : Fin 372,
    rowEval (d1Row 59) (fun j => if j = e then 1 else 0) =
      (if 59 = (edge e).2 then 1 else 0) -
      (if 59 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_5_oai (i : Fin 103) (hb : 50 ≤ i.val ∧ i.val < 60) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_50 e
  · exact d1_basis_cert_51 e
  · exact d1_basis_cert_52 e
  · exact d1_basis_cert_53 e
  · exact d1_basis_cert_54 e
  · exact d1_basis_cert_55 e
  · exact d1_basis_cert_56 e
  · exact d1_basis_cert_57 e
  · exact d1_basis_cert_58 e
  · exact d1_basis_cert_59 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_5_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_5_oai
