-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:36:01.497552+00:00
-- url     : https://prove2.me/submissions/6ff69b0d-16d6-4c46-ba63-93b592304b73

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

theorem d1_basis_cert_70 : ∀ e : Fin 372,
    rowEval (d1Row 70) (fun j => if j = e then 1 else 0) =
      (if 70 = (edge e).2 then 1 else 0) -
      (if 70 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_71 : ∀ e : Fin 372,
    rowEval (d1Row 71) (fun j => if j = e then 1 else 0) =
      (if 71 = (edge e).2 then 1 else 0) -
      (if 71 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_72 : ∀ e : Fin 372,
    rowEval (d1Row 72) (fun j => if j = e then 1 else 0) =
      (if 72 = (edge e).2 then 1 else 0) -
      (if 72 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_73 : ∀ e : Fin 372,
    rowEval (d1Row 73) (fun j => if j = e then 1 else 0) =
      (if 73 = (edge e).2 then 1 else 0) -
      (if 73 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_74 : ∀ e : Fin 372,
    rowEval (d1Row 74) (fun j => if j = e then 1 else 0) =
      (if 74 = (edge e).2 then 1 else 0) -
      (if 74 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_75 : ∀ e : Fin 372,
    rowEval (d1Row 75) (fun j => if j = e then 1 else 0) =
      (if 75 = (edge e).2 then 1 else 0) -
      (if 75 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_76 : ∀ e : Fin 372,
    rowEval (d1Row 76) (fun j => if j = e then 1 else 0) =
      (if 76 = (edge e).2 then 1 else 0) -
      (if 76 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_77 : ∀ e : Fin 372,
    rowEval (d1Row 77) (fun j => if j = e then 1 else 0) =
      (if 77 = (edge e).2 then 1 else 0) -
      (if 77 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_78 : ∀ e : Fin 372,
    rowEval (d1Row 78) (fun j => if j = e then 1 else 0) =
      (if 78 = (edge e).2 then 1 else 0) -
      (if 78 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_79 : ∀ e : Fin 372,
    rowEval (d1Row 79) (fun j => if j = e then 1 else 0) =
      (if 79 = (edge e).2 then 1 else 0) -
      (if 79 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_7_oai (i : Fin 103) (hb : 70 ≤ i.val ∧ i.val < 80) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_70 e
  · exact d1_basis_cert_71 e
  · exact d1_basis_cert_72 e
  · exact d1_basis_cert_73 e
  · exact d1_basis_cert_74 e
  · exact d1_basis_cert_75 e
  · exact d1_basis_cert_76 e
  · exact d1_basis_cert_77 e
  · exact d1_basis_cert_78 e
  · exact d1_basis_cert_79 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_7_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_7_oai
