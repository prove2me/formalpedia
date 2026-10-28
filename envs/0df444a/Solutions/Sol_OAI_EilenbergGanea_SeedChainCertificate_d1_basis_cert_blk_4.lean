-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:33:07.210145+00:00
-- url     : https://prove2.me/submissions/a79dc64e-98c9-4fa7-b5e8-8ad97e195bf2

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

theorem d1_basis_cert_40 : ∀ e : Fin 372,
    rowEval (d1Row 40) (fun j => if j = e then 1 else 0) =
      (if 40 = (edge e).2 then 1 else 0) -
      (if 40 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_41 : ∀ e : Fin 372,
    rowEval (d1Row 41) (fun j => if j = e then 1 else 0) =
      (if 41 = (edge e).2 then 1 else 0) -
      (if 41 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_42 : ∀ e : Fin 372,
    rowEval (d1Row 42) (fun j => if j = e then 1 else 0) =
      (if 42 = (edge e).2 then 1 else 0) -
      (if 42 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_43 : ∀ e : Fin 372,
    rowEval (d1Row 43) (fun j => if j = e then 1 else 0) =
      (if 43 = (edge e).2 then 1 else 0) -
      (if 43 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_44 : ∀ e : Fin 372,
    rowEval (d1Row 44) (fun j => if j = e then 1 else 0) =
      (if 44 = (edge e).2 then 1 else 0) -
      (if 44 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_45 : ∀ e : Fin 372,
    rowEval (d1Row 45) (fun j => if j = e then 1 else 0) =
      (if 45 = (edge e).2 then 1 else 0) -
      (if 45 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_46 : ∀ e : Fin 372,
    rowEval (d1Row 46) (fun j => if j = e then 1 else 0) =
      (if 46 = (edge e).2 then 1 else 0) -
      (if 46 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_47 : ∀ e : Fin 372,
    rowEval (d1Row 47) (fun j => if j = e then 1 else 0) =
      (if 47 = (edge e).2 then 1 else 0) -
      (if 47 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_48 : ∀ e : Fin 372,
    rowEval (d1Row 48) (fun j => if j = e then 1 else 0) =
      (if 48 = (edge e).2 then 1 else 0) -
      (if 48 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_49 : ∀ e : Fin 372,
    rowEval (d1Row 49) (fun j => if j = e then 1 else 0) =
      (if 49 = (edge e).2 then 1 else 0) -
      (if 49 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_4_oai (i : Fin 103) (hb : 40 ≤ i.val ∧ i.val < 50) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_40 e
  · exact d1_basis_cert_41 e
  · exact d1_basis_cert_42 e
  · exact d1_basis_cert_43 e
  · exact d1_basis_cert_44 e
  · exact d1_basis_cert_45 e
  · exact d1_basis_cert_46 e
  · exact d1_basis_cert_47 e
  · exact d1_basis_cert_48 e
  · exact d1_basis_cert_49 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_4_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_4_oai
