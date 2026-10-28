-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:14:10.395489+00:00
-- url     : https://prove2.me/submissions/dd8e8cf3-cc22-4191-be6e-a7aaef8836df

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

theorem d2_basis_cert_60 : ∀ t : Fin 270,
    rowEval (d2Row 60) (fun j => if j = t then 1 else 0) =
      (if 60 = (triangleEdges t).1 then 1 else 0) -
      (if 60 = (triangleEdges t).2.1 then 1 else 0) +
      (if 60 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_61 : ∀ t : Fin 270,
    rowEval (d2Row 61) (fun j => if j = t then 1 else 0) =
      (if 61 = (triangleEdges t).1 then 1 else 0) -
      (if 61 = (triangleEdges t).2.1 then 1 else 0) +
      (if 61 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_62 : ∀ t : Fin 270,
    rowEval (d2Row 62) (fun j => if j = t then 1 else 0) =
      (if 62 = (triangleEdges t).1 then 1 else 0) -
      (if 62 = (triangleEdges t).2.1 then 1 else 0) +
      (if 62 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_63 : ∀ t : Fin 270,
    rowEval (d2Row 63) (fun j => if j = t then 1 else 0) =
      (if 63 = (triangleEdges t).1 then 1 else 0) -
      (if 63 = (triangleEdges t).2.1 then 1 else 0) +
      (if 63 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_64 : ∀ t : Fin 270,
    rowEval (d2Row 64) (fun j => if j = t then 1 else 0) =
      (if 64 = (triangleEdges t).1 then 1 else 0) -
      (if 64 = (triangleEdges t).2.1 then 1 else 0) +
      (if 64 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_65 : ∀ t : Fin 270,
    rowEval (d2Row 65) (fun j => if j = t then 1 else 0) =
      (if 65 = (triangleEdges t).1 then 1 else 0) -
      (if 65 = (triangleEdges t).2.1 then 1 else 0) +
      (if 65 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_66 : ∀ t : Fin 270,
    rowEval (d2Row 66) (fun j => if j = t then 1 else 0) =
      (if 66 = (triangleEdges t).1 then 1 else 0) -
      (if 66 = (triangleEdges t).2.1 then 1 else 0) +
      (if 66 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_67 : ∀ t : Fin 270,
    rowEval (d2Row 67) (fun j => if j = t then 1 else 0) =
      (if 67 = (triangleEdges t).1 then 1 else 0) -
      (if 67 = (triangleEdges t).2.1 then 1 else 0) +
      (if 67 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_68 : ∀ t : Fin 270,
    rowEval (d2Row 68) (fun j => if j = t then 1 else 0) =
      (if 68 = (triangleEdges t).1 then 1 else 0) -
      (if 68 = (triangleEdges t).2.1 then 1 else 0) +
      (if 68 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_69 : ∀ t : Fin 270,
    rowEval (d2Row 69) (fun j => if j = t then 1 else 0) =
      (if 69 = (triangleEdges t).1 then 1 else 0) -
      (if 69 = (triangleEdges t).2.1 then 1 else 0) +
      (if 69 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_70 : ∀ t : Fin 270,
    rowEval (d2Row 70) (fun j => if j = t then 1 else 0) =
      (if 70 = (triangleEdges t).1 then 1 else 0) -
      (if 70 = (triangleEdges t).2.1 then 1 else 0) +
      (if 70 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_71 : ∀ t : Fin 270,
    rowEval (d2Row 71) (fun j => if j = t then 1 else 0) =
      (if 71 = (triangleEdges t).1 then 1 else 0) -
      (if 71 = (triangleEdges t).2.1 then 1 else 0) +
      (if 71 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_72 : ∀ t : Fin 270,
    rowEval (d2Row 72) (fun j => if j = t then 1 else 0) =
      (if 72 = (triangleEdges t).1 then 1 else 0) -
      (if 72 = (triangleEdges t).2.1 then 1 else 0) +
      (if 72 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_73 : ∀ t : Fin 270,
    rowEval (d2Row 73) (fun j => if j = t then 1 else 0) =
      (if 73 = (triangleEdges t).1 then 1 else 0) -
      (if 73 = (triangleEdges t).2.1 then 1 else 0) +
      (if 73 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_74 : ∀ t : Fin 270,
    rowEval (d2Row 74) (fun j => if j = t then 1 else 0) =
      (if 74 = (triangleEdges t).1 then 1 else 0) -
      (if 74 = (triangleEdges t).2.1 then 1 else 0) +
      (if 74 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_75 : ∀ t : Fin 270,
    rowEval (d2Row 75) (fun j => if j = t then 1 else 0) =
      (if 75 = (triangleEdges t).1 then 1 else 0) -
      (if 75 = (triangleEdges t).2.1 then 1 else 0) +
      (if 75 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_76 : ∀ t : Fin 270,
    rowEval (d2Row 76) (fun j => if j = t then 1 else 0) =
      (if 76 = (triangleEdges t).1 then 1 else 0) -
      (if 76 = (triangleEdges t).2.1 then 1 else 0) +
      (if 76 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_77 : ∀ t : Fin 270,
    rowEval (d2Row 77) (fun j => if j = t then 1 else 0) =
      (if 77 = (triangleEdges t).1 then 1 else 0) -
      (if 77 = (triangleEdges t).2.1 then 1 else 0) +
      (if 77 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_78 : ∀ t : Fin 270,
    rowEval (d2Row 78) (fun j => if j = t then 1 else 0) =
      (if 78 = (triangleEdges t).1 then 1 else 0) -
      (if 78 = (triangleEdges t).2.1 then 1 else 0) +
      (if 78 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_79 : ∀ t : Fin 270,
    rowEval (d2Row 79) (fun j => if j = t then 1 else 0) =
      (if 79 = (triangleEdges t).1 then 1 else 0) -
      (if 79 = (triangleEdges t).2.1 then 1 else 0) +
      (if 79 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_80 : ∀ t : Fin 270,
    rowEval (d2Row 80) (fun j => if j = t then 1 else 0) =
      (if 80 = (triangleEdges t).1 then 1 else 0) -
      (if 80 = (triangleEdges t).2.1 then 1 else 0) +
      (if 80 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_81 : ∀ t : Fin 270,
    rowEval (d2Row 81) (fun j => if j = t then 1 else 0) =
      (if 81 = (triangleEdges t).1 then 1 else 0) -
      (if 81 = (triangleEdges t).2.1 then 1 else 0) +
      (if 81 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_82 : ∀ t : Fin 270,
    rowEval (d2Row 82) (fun j => if j = t then 1 else 0) =
      (if 82 = (triangleEdges t).1 then 1 else 0) -
      (if 82 = (triangleEdges t).2.1 then 1 else 0) +
      (if 82 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_83 : ∀ t : Fin 270,
    rowEval (d2Row 83) (fun j => if j = t then 1 else 0) =
      (if 83 = (triangleEdges t).1 then 1 else 0) -
      (if 83 = (triangleEdges t).2.1 then 1 else 0) +
      (if 83 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_84 : ∀ t : Fin 270,
    rowEval (d2Row 84) (fun j => if j = t then 1 else 0) =
      (if 84 = (triangleEdges t).1 then 1 else 0) -
      (if 84 = (triangleEdges t).2.1 then 1 else 0) +
      (if 84 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_85 : ∀ t : Fin 270,
    rowEval (d2Row 85) (fun j => if j = t then 1 else 0) =
      (if 85 = (triangleEdges t).1 then 1 else 0) -
      (if 85 = (triangleEdges t).2.1 then 1 else 0) +
      (if 85 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_86 : ∀ t : Fin 270,
    rowEval (d2Row 86) (fun j => if j = t then 1 else 0) =
      (if 86 = (triangleEdges t).1 then 1 else 0) -
      (if 86 = (triangleEdges t).2.1 then 1 else 0) +
      (if 86 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_87 : ∀ t : Fin 270,
    rowEval (d2Row 87) (fun j => if j = t then 1 else 0) =
      (if 87 = (triangleEdges t).1 then 1 else 0) -
      (if 87 = (triangleEdges t).2.1 then 1 else 0) +
      (if 87 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_88 : ∀ t : Fin 270,
    rowEval (d2Row 88) (fun j => if j = t then 1 else 0) =
      (if 88 = (triangleEdges t).1 then 1 else 0) -
      (if 88 = (triangleEdges t).2.1 then 1 else 0) +
      (if 88 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_89 : ∀ t : Fin 270,
    rowEval (d2Row 89) (fun j => if j = t then 1 else 0) =
      (if 89 = (triangleEdges t).1 then 1 else 0) -
      (if 89 = (triangleEdges t).2.1 then 1 else 0) +
      (if 89 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_2_oai (e : Fin 372) (hb : 60 ≤ e.val ∧ e.val < 90) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_60 t
  · exact d2_basis_cert_61 t
  · exact d2_basis_cert_62 t
  · exact d2_basis_cert_63 t
  · exact d2_basis_cert_64 t
  · exact d2_basis_cert_65 t
  · exact d2_basis_cert_66 t
  · exact d2_basis_cert_67 t
  · exact d2_basis_cert_68 t
  · exact d2_basis_cert_69 t
  · exact d2_basis_cert_70 t
  · exact d2_basis_cert_71 t
  · exact d2_basis_cert_72 t
  · exact d2_basis_cert_73 t
  · exact d2_basis_cert_74 t
  · exact d2_basis_cert_75 t
  · exact d2_basis_cert_76 t
  · exact d2_basis_cert_77 t
  · exact d2_basis_cert_78 t
  · exact d2_basis_cert_79 t
  · exact d2_basis_cert_80 t
  · exact d2_basis_cert_81 t
  · exact d2_basis_cert_82 t
  · exact d2_basis_cert_83 t
  · exact d2_basis_cert_84 t
  · exact d2_basis_cert_85 t
  · exact d2_basis_cert_86 t
  · exact d2_basis_cert_87 t
  · exact d2_basis_cert_88 t
  · exact d2_basis_cert_89 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_2_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_2_oai
