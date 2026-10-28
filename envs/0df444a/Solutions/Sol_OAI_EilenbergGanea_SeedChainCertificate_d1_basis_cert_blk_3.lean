-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:32:23.051775+00:00
-- url     : https://prove2.me/submissions/8ec4267c-ae28-4da2-8543-4b43302b426e

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

theorem d1_basis_cert_30 : ∀ e : Fin 372,
    rowEval (d1Row 30) (fun j => if j = e then 1 else 0) =
      (if 30 = (edge e).2 then 1 else 0) -
      (if 30 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_31 : ∀ e : Fin 372,
    rowEval (d1Row 31) (fun j => if j = e then 1 else 0) =
      (if 31 = (edge e).2 then 1 else 0) -
      (if 31 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_32 : ∀ e : Fin 372,
    rowEval (d1Row 32) (fun j => if j = e then 1 else 0) =
      (if 32 = (edge e).2 then 1 else 0) -
      (if 32 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_33 : ∀ e : Fin 372,
    rowEval (d1Row 33) (fun j => if j = e then 1 else 0) =
      (if 33 = (edge e).2 then 1 else 0) -
      (if 33 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_34 : ∀ e : Fin 372,
    rowEval (d1Row 34) (fun j => if j = e then 1 else 0) =
      (if 34 = (edge e).2 then 1 else 0) -
      (if 34 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_35 : ∀ e : Fin 372,
    rowEval (d1Row 35) (fun j => if j = e then 1 else 0) =
      (if 35 = (edge e).2 then 1 else 0) -
      (if 35 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_36 : ∀ e : Fin 372,
    rowEval (d1Row 36) (fun j => if j = e then 1 else 0) =
      (if 36 = (edge e).2 then 1 else 0) -
      (if 36 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_37 : ∀ e : Fin 372,
    rowEval (d1Row 37) (fun j => if j = e then 1 else 0) =
      (if 37 = (edge e).2 then 1 else 0) -
      (if 37 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_38 : ∀ e : Fin 372,
    rowEval (d1Row 38) (fun j => if j = e then 1 else 0) =
      (if 38 = (edge e).2 then 1 else 0) -
      (if 38 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_39 : ∀ e : Fin 372,
    rowEval (d1Row 39) (fun j => if j = e then 1 else 0) =
      (if 39 = (edge e).2 then 1 else 0) -
      (if 39 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_3_oai (i : Fin 103) (hb : 30 ≤ i.val ∧ i.val < 40) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_30 e
  · exact d1_basis_cert_31 e
  · exact d1_basis_cert_32 e
  · exact d1_basis_cert_33 e
  · exact d1_basis_cert_34 e
  · exact d1_basis_cert_35 e
  · exact d1_basis_cert_36 e
  · exact d1_basis_cert_37 e
  · exact d1_basis_cert_38 e
  · exact d1_basis_cert_39 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_3_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_3_oai
