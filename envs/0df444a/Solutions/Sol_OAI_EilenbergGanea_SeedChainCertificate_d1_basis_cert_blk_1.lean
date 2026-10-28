-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:28:21.597164+00:00
-- url     : https://prove2.me/submissions/b6dec606-317e-4a3d-84a4-137f6f76ed48

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

theorem d1_basis_cert_10 : ∀ e : Fin 372,
    rowEval (d1Row 10) (fun j => if j = e then 1 else 0) =
      (if 10 = (edge e).2 then 1 else 0) -
      (if 10 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_11 : ∀ e : Fin 372,
    rowEval (d1Row 11) (fun j => if j = e then 1 else 0) =
      (if 11 = (edge e).2 then 1 else 0) -
      (if 11 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_12 : ∀ e : Fin 372,
    rowEval (d1Row 12) (fun j => if j = e then 1 else 0) =
      (if 12 = (edge e).2 then 1 else 0) -
      (if 12 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_13 : ∀ e : Fin 372,
    rowEval (d1Row 13) (fun j => if j = e then 1 else 0) =
      (if 13 = (edge e).2 then 1 else 0) -
      (if 13 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_14 : ∀ e : Fin 372,
    rowEval (d1Row 14) (fun j => if j = e then 1 else 0) =
      (if 14 = (edge e).2 then 1 else 0) -
      (if 14 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_15 : ∀ e : Fin 372,
    rowEval (d1Row 15) (fun j => if j = e then 1 else 0) =
      (if 15 = (edge e).2 then 1 else 0) -
      (if 15 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_16 : ∀ e : Fin 372,
    rowEval (d1Row 16) (fun j => if j = e then 1 else 0) =
      (if 16 = (edge e).2 then 1 else 0) -
      (if 16 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_17 : ∀ e : Fin 372,
    rowEval (d1Row 17) (fun j => if j = e then 1 else 0) =
      (if 17 = (edge e).2 then 1 else 0) -
      (if 17 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_18 : ∀ e : Fin 372,
    rowEval (d1Row 18) (fun j => if j = e then 1 else 0) =
      (if 18 = (edge e).2 then 1 else 0) -
      (if 18 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_19 : ∀ e : Fin 372,
    rowEval (d1Row 19) (fun j => if j = e then 1 else 0) =
      (if 19 = (edge e).2 then 1 else 0) -
      (if 19 = (edge e).1 then 1 else 0) := by decide +kernel

theorem d1_basis_cert_blk_1_oai (i : Fin 103) (hb : 10 ≤ i.val ∧ i.val < 20) (e : Fin 372) :
    rowEval (d1Row i) (fun j => if j = e then 1 else 0) =
      (if i = (edge e).2 then 1 else 0) - (if i = (edge e).1 then 1 else 0) := by
  rcases i with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d1_basis_cert_10 e
  · exact d1_basis_cert_11 e
  · exact d1_basis_cert_12 e
  · exact d1_basis_cert_13 e
  · exact d1_basis_cert_14 e
  · exact d1_basis_cert_15 e
  · exact d1_basis_cert_16 e
  · exact d1_basis_cert_17 e
  · exact d1_basis_cert_18 e
  · exact d1_basis_cert_19 e

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_1_oai := @OAI.EilenbergGanea.SeedChainCertificate.d1_basis_cert_blk_1_oai
