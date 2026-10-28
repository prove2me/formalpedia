-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:20.551153+00:00
-- url     : https://prove2.me/submissions/1713f9a6-0c67-48b3-85f6-c857ef33f29f

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

theorem d1_basis_cert_0 : ∀ e : Fin 372,
    rowEval (d1Row 0) (fun j => if j = e then 1 else 0) =
      (if 0 = (edge e).2 then 1 else 0) -
      (if 0 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_1 : ∀ e : Fin 372,
    rowEval (d1Row 1) (fun j => if j = e then 1 else 0) =
      (if 1 = (edge e).2 then 1 else 0) -
      (if 1 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_2 : ∀ e : Fin 372,
    rowEval (d1Row 2) (fun j => if j = e then 1 else 0) =
      (if 2 = (edge e).2 then 1 else 0) -
      (if 2 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_3 : ∀ e : Fin 372,
    rowEval (d1Row 3) (fun j => if j = e then 1 else 0) =
      (if 3 = (edge e).2 then 1 else 0) -
      (if 3 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_4 : ∀ e : Fin 372,
    rowEval (d1Row 4) (fun j => if j = e then 1 else 0) =
      (if 4 = (edge e).2 then 1 else 0) -
      (if 4 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_5 : ∀ e : Fin 372,
    rowEval (d1Row 5) (fun j => if j = e then 1 else 0) =
      (if 5 = (edge e).2 then 1 else 0) -
      (if 5 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_6 : ∀ e : Fin 372,
    rowEval (d1Row 6) (fun j => if j = e then 1 else 0) =
      (if 6 = (edge e).2 then 1 else 0) -
      (if 6 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_7 : ∀ e : Fin 372,
    rowEval (d1Row 7) (fun j => if j = e then 1 else 0) =
      (if 7 = (edge e).2 then 1 else 0) -
      (if 7 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_8 : ∀ e : Fin 372,
    rowEval (d1Row 8) (fun j => if j = e then 1 else 0) =
      (if 8 = (edge e).2 then 1 else 0) -
      (if 8 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_9 : ∀ e : Fin 372,
    rowEval (d1Row 9) (fun j => if j = e then 1 else 0) =
      (if 9 = (edge e).2 then 1 else 0) -
      (if 9 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_0_oai (i : Fin 103) (hb : 0 ≤ i.val ∧ i.val < 10) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_0 e
  · exact d1_basis_cert_1 e
  · exact d1_basis_cert_2 e
  · exact d1_basis_cert_3 e
  · exact d1_basis_cert_4 e
  · exact d1_basis_cert_5 e
  · exact d1_basis_cert_6 e
  · exact d1_basis_cert_7 e
  · exact d1_basis_cert_8 e
  · exact d1_basis_cert_9 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_0_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_0_oai
