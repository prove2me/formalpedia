-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:34:56.46995+00:00
-- url     : https://prove2.me/submissions/8186afb8-53e4-40f7-befd-b78a123d079d

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

theorem d1_basis_cert_60 : ∀ e : Fin 372,
    rowEval (d1Row 60) (fun j => if j = e then 1 else 0) =
      (if 60 = (edge e).2 then 1 else 0) -
      (if 60 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_61 : ∀ e : Fin 372,
    rowEval (d1Row 61) (fun j => if j = e then 1 else 0) =
      (if 61 = (edge e).2 then 1 else 0) -
      (if 61 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_62 : ∀ e : Fin 372,
    rowEval (d1Row 62) (fun j => if j = e then 1 else 0) =
      (if 62 = (edge e).2 then 1 else 0) -
      (if 62 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_63 : ∀ e : Fin 372,
    rowEval (d1Row 63) (fun j => if j = e then 1 else 0) =
      (if 63 = (edge e).2 then 1 else 0) -
      (if 63 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_64 : ∀ e : Fin 372,
    rowEval (d1Row 64) (fun j => if j = e then 1 else 0) =
      (if 64 = (edge e).2 then 1 else 0) -
      (if 64 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_65 : ∀ e : Fin 372,
    rowEval (d1Row 65) (fun j => if j = e then 1 else 0) =
      (if 65 = (edge e).2 then 1 else 0) -
      (if 65 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_66 : ∀ e : Fin 372,
    rowEval (d1Row 66) (fun j => if j = e then 1 else 0) =
      (if 66 = (edge e).2 then 1 else 0) -
      (if 66 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_67 : ∀ e : Fin 372,
    rowEval (d1Row 67) (fun j => if j = e then 1 else 0) =
      (if 67 = (edge e).2 then 1 else 0) -
      (if 67 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_68 : ∀ e : Fin 372,
    rowEval (d1Row 68) (fun j => if j = e then 1 else 0) =
      (if 68 = (edge e).2 then 1 else 0) -
      (if 68 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_69 : ∀ e : Fin 372,
    rowEval (d1Row 69) (fun j => if j = e then 1 else 0) =
      (if 69 = (edge e).2 then 1 else 0) -
      (if 69 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_6_oai (i : Fin 103) (hb : 60 ≤ i.val ∧ i.val < 70) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_60 e
  · exact d1_basis_cert_61 e
  · exact d1_basis_cert_62 e
  · exact d1_basis_cert_63 e
  · exact d1_basis_cert_64 e
  · exact d1_basis_cert_65 e
  · exact d1_basis_cert_66 e
  · exact d1_basis_cert_67 e
  · exact d1_basis_cert_68 e
  · exact d1_basis_cert_69 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_6_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_6_oai
