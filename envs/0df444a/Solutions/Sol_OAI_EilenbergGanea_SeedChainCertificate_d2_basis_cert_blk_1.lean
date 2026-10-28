-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:02:25.868485+00:00
-- url     : https://prove2.me/submissions/61b3369c-de8c-427b-974d-25ce6550453e

import Mathlib
import Definitions.Def_OAIEG001
import Definitions.Def_OAIEG002

section
-- module Solutions.OAIEG.SeedContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem d2_basis_cert_30 : ∀ t : Fin 270,
    rowEval (d2Row 30) (fun j => if j = t then 1 else 0) =
      (if 30 = (triangleEdges t).1 then 1 else 0) -
      (if 30 = (triangleEdges t).2.1 then 1 else 0) +
      (if 30 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_31 : ∀ t : Fin 270,
    rowEval (d2Row 31) (fun j => if j = t then 1 else 0) =
      (if 31 = (triangleEdges t).1 then 1 else 0) -
      (if 31 = (triangleEdges t).2.1 then 1 else 0) +
      (if 31 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_32 : ∀ t : Fin 270,
    rowEval (d2Row 32) (fun j => if j = t then 1 else 0) =
      (if 32 = (triangleEdges t).1 then 1 else 0) -
      (if 32 = (triangleEdges t).2.1 then 1 else 0) +
      (if 32 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_33 : ∀ t : Fin 270,
    rowEval (d2Row 33) (fun j => if j = t then 1 else 0) =
      (if 33 = (triangleEdges t).1 then 1 else 0) -
      (if 33 = (triangleEdges t).2.1 then 1 else 0) +
      (if 33 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_34 : ∀ t : Fin 270,
    rowEval (d2Row 34) (fun j => if j = t then 1 else 0) =
      (if 34 = (triangleEdges t).1 then 1 else 0) -
      (if 34 = (triangleEdges t).2.1 then 1 else 0) +
      (if 34 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_35 : ∀ t : Fin 270,
    rowEval (d2Row 35) (fun j => if j = t then 1 else 0) =
      (if 35 = (triangleEdges t).1 then 1 else 0) -
      (if 35 = (triangleEdges t).2.1 then 1 else 0) +
      (if 35 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_36 : ∀ t : Fin 270,
    rowEval (d2Row 36) (fun j => if j = t then 1 else 0) =
      (if 36 = (triangleEdges t).1 then 1 else 0) -
      (if 36 = (triangleEdges t).2.1 then 1 else 0) +
      (if 36 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_37 : ∀ t : Fin 270,
    rowEval (d2Row 37) (fun j => if j = t then 1 else 0) =
      (if 37 = (triangleEdges t).1 then 1 else 0) -
      (if 37 = (triangleEdges t).2.1 then 1 else 0) +
      (if 37 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_38 : ∀ t : Fin 270,
    rowEval (d2Row 38) (fun j => if j = t then 1 else 0) =
      (if 38 = (triangleEdges t).1 then 1 else 0) -
      (if 38 = (triangleEdges t).2.1 then 1 else 0) +
      (if 38 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_39 : ∀ t : Fin 270,
    rowEval (d2Row 39) (fun j => if j = t then 1 else 0) =
      (if 39 = (triangleEdges t).1 then 1 else 0) -
      (if 39 = (triangleEdges t).2.1 then 1 else 0) +
      (if 39 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_40 : ∀ t : Fin 270,
    rowEval (d2Row 40) (fun j => if j = t then 1 else 0) =
      (if 40 = (triangleEdges t).1 then 1 else 0) -
      (if 40 = (triangleEdges t).2.1 then 1 else 0) +
      (if 40 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_41 : ∀ t : Fin 270,
    rowEval (d2Row 41) (fun j => if j = t then 1 else 0) =
      (if 41 = (triangleEdges t).1 then 1 else 0) -
      (if 41 = (triangleEdges t).2.1 then 1 else 0) +
      (if 41 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_42 : ∀ t : Fin 270,
    rowEval (d2Row 42) (fun j => if j = t then 1 else 0) =
      (if 42 = (triangleEdges t).1 then 1 else 0) -
      (if 42 = (triangleEdges t).2.1 then 1 else 0) +
      (if 42 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_43 : ∀ t : Fin 270,
    rowEval (d2Row 43) (fun j => if j = t then 1 else 0) =
      (if 43 = (triangleEdges t).1 then 1 else 0) -
      (if 43 = (triangleEdges t).2.1 then 1 else 0) +
      (if 43 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_44 : ∀ t : Fin 270,
    rowEval (d2Row 44) (fun j => if j = t then 1 else 0) =
      (if 44 = (triangleEdges t).1 then 1 else 0) -
      (if 44 = (triangleEdges t).2.1 then 1 else 0) +
      (if 44 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_45 : ∀ t : Fin 270,
    rowEval (d2Row 45) (fun j => if j = t then 1 else 0) =
      (if 45 = (triangleEdges t).1 then 1 else 0) -
      (if 45 = (triangleEdges t).2.1 then 1 else 0) +
      (if 45 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_46 : ∀ t : Fin 270,
    rowEval (d2Row 46) (fun j => if j = t then 1 else 0) =
      (if 46 = (triangleEdges t).1 then 1 else 0) -
      (if 46 = (triangleEdges t).2.1 then 1 else 0) +
      (if 46 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_47 : ∀ t : Fin 270,
    rowEval (d2Row 47) (fun j => if j = t then 1 else 0) =
      (if 47 = (triangleEdges t).1 then 1 else 0) -
      (if 47 = (triangleEdges t).2.1 then 1 else 0) +
      (if 47 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_48 : ∀ t : Fin 270,
    rowEval (d2Row 48) (fun j => if j = t then 1 else 0) =
      (if 48 = (triangleEdges t).1 then 1 else 0) -
      (if 48 = (triangleEdges t).2.1 then 1 else 0) +
      (if 48 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_49 : ∀ t : Fin 270,
    rowEval (d2Row 49) (fun j => if j = t then 1 else 0) =
      (if 49 = (triangleEdges t).1 then 1 else 0) -
      (if 49 = (triangleEdges t).2.1 then 1 else 0) +
      (if 49 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_50 : ∀ t : Fin 270,
    rowEval (d2Row 50) (fun j => if j = t then 1 else 0) =
      (if 50 = (triangleEdges t).1 then 1 else 0) -
      (if 50 = (triangleEdges t).2.1 then 1 else 0) +
      (if 50 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_51 : ∀ t : Fin 270,
    rowEval (d2Row 51) (fun j => if j = t then 1 else 0) =
      (if 51 = (triangleEdges t).1 then 1 else 0) -
      (if 51 = (triangleEdges t).2.1 then 1 else 0) +
      (if 51 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_52 : ∀ t : Fin 270,
    rowEval (d2Row 52) (fun j => if j = t then 1 else 0) =
      (if 52 = (triangleEdges t).1 then 1 else 0) -
      (if 52 = (triangleEdges t).2.1 then 1 else 0) +
      (if 52 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_53 : ∀ t : Fin 270,
    rowEval (d2Row 53) (fun j => if j = t then 1 else 0) =
      (if 53 = (triangleEdges t).1 then 1 else 0) -
      (if 53 = (triangleEdges t).2.1 then 1 else 0) +
      (if 53 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_54 : ∀ t : Fin 270,
    rowEval (d2Row 54) (fun j => if j = t then 1 else 0) =
      (if 54 = (triangleEdges t).1 then 1 else 0) -
      (if 54 = (triangleEdges t).2.1 then 1 else 0) +
      (if 54 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_55 : ∀ t : Fin 270,
    rowEval (d2Row 55) (fun j => if j = t then 1 else 0) =
      (if 55 = (triangleEdges t).1 then 1 else 0) -
      (if 55 = (triangleEdges t).2.1 then 1 else 0) +
      (if 55 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_56 : ∀ t : Fin 270,
    rowEval (d2Row 56) (fun j => if j = t then 1 else 0) =
      (if 56 = (triangleEdges t).1 then 1 else 0) -
      (if 56 = (triangleEdges t).2.1 then 1 else 0) +
      (if 56 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_57 : ∀ t : Fin 270,
    rowEval (d2Row 57) (fun j => if j = t then 1 else 0) =
      (if 57 = (triangleEdges t).1 then 1 else 0) -
      (if 57 = (triangleEdges t).2.1 then 1 else 0) +
      (if 57 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_58 : ∀ t : Fin 270,
    rowEval (d2Row 58) (fun j => if j = t then 1 else 0) =
      (if 58 = (triangleEdges t).1 then 1 else 0) -
      (if 58 = (triangleEdges t).2.1 then 1 else 0) +
      (if 58 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_59 : ∀ t : Fin 270,
    rowEval (d2Row 59) (fun j => if j = t then 1 else 0) =
      (if 59 = (triangleEdges t).1 then 1 else 0) -
      (if 59 = (triangleEdges t).2.1 then 1 else 0) +
      (if 59 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_1_oai (e : Fin 372) (hb : 30 ≤ e.val ∧ e.val < 60) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_30 t
  · exact d2_basis_cert_31 t
  · exact d2_basis_cert_32 t
  · exact d2_basis_cert_33 t
  · exact d2_basis_cert_34 t
  · exact d2_basis_cert_35 t
  · exact d2_basis_cert_36 t
  · exact d2_basis_cert_37 t
  · exact d2_basis_cert_38 t
  · exact d2_basis_cert_39 t
  · exact d2_basis_cert_40 t
  · exact d2_basis_cert_41 t
  · exact d2_basis_cert_42 t
  · exact d2_basis_cert_43 t
  · exact d2_basis_cert_44 t
  · exact d2_basis_cert_45 t
  · exact d2_basis_cert_46 t
  · exact d2_basis_cert_47 t
  · exact d2_basis_cert_48 t
  · exact d2_basis_cert_49 t
  · exact d2_basis_cert_50 t
  · exact d2_basis_cert_51 t
  · exact d2_basis_cert_52 t
  · exact d2_basis_cert_53 t
  · exact d2_basis_cert_54 t
  · exact d2_basis_cert_55 t
  · exact d2_basis_cert_56 t
  · exact d2_basis_cert_57 t
  · exact d2_basis_cert_58 t
  · exact d2_basis_cert_59 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_1_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_1_oai
