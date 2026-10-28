-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:14:11.401017+00:00
-- url     : https://prove2.me/submissions/ad40434e-005b-405f-a30f-3e27687b2d61

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

theorem d2_basis_cert_90 : ∀ t : Fin 270,
    rowEval (d2Row 90) (fun j => if j = t then 1 else 0) =
      (if 90 = (triangleEdges t).1 then 1 else 0) -
      (if 90 = (triangleEdges t).2.1 then 1 else 0) +
      (if 90 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_91 : ∀ t : Fin 270,
    rowEval (d2Row 91) (fun j => if j = t then 1 else 0) =
      (if 91 = (triangleEdges t).1 then 1 else 0) -
      (if 91 = (triangleEdges t).2.1 then 1 else 0) +
      (if 91 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_92 : ∀ t : Fin 270,
    rowEval (d2Row 92) (fun j => if j = t then 1 else 0) =
      (if 92 = (triangleEdges t).1 then 1 else 0) -
      (if 92 = (triangleEdges t).2.1 then 1 else 0) +
      (if 92 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_93 : ∀ t : Fin 270,
    rowEval (d2Row 93) (fun j => if j = t then 1 else 0) =
      (if 93 = (triangleEdges t).1 then 1 else 0) -
      (if 93 = (triangleEdges t).2.1 then 1 else 0) +
      (if 93 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_94 : ∀ t : Fin 270,
    rowEval (d2Row 94) (fun j => if j = t then 1 else 0) =
      (if 94 = (triangleEdges t).1 then 1 else 0) -
      (if 94 = (triangleEdges t).2.1 then 1 else 0) +
      (if 94 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_95 : ∀ t : Fin 270,
    rowEval (d2Row 95) (fun j => if j = t then 1 else 0) =
      (if 95 = (triangleEdges t).1 then 1 else 0) -
      (if 95 = (triangleEdges t).2.1 then 1 else 0) +
      (if 95 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_96 : ∀ t : Fin 270,
    rowEval (d2Row 96) (fun j => if j = t then 1 else 0) =
      (if 96 = (triangleEdges t).1 then 1 else 0) -
      (if 96 = (triangleEdges t).2.1 then 1 else 0) +
      (if 96 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_97 : ∀ t : Fin 270,
    rowEval (d2Row 97) (fun j => if j = t then 1 else 0) =
      (if 97 = (triangleEdges t).1 then 1 else 0) -
      (if 97 = (triangleEdges t).2.1 then 1 else 0) +
      (if 97 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_98 : ∀ t : Fin 270,
    rowEval (d2Row 98) (fun j => if j = t then 1 else 0) =
      (if 98 = (triangleEdges t).1 then 1 else 0) -
      (if 98 = (triangleEdges t).2.1 then 1 else 0) +
      (if 98 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_99 : ∀ t : Fin 270,
    rowEval (d2Row 99) (fun j => if j = t then 1 else 0) =
      (if 99 = (triangleEdges t).1 then 1 else 0) -
      (if 99 = (triangleEdges t).2.1 then 1 else 0) +
      (if 99 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_100 : ∀ t : Fin 270,
    rowEval (d2Row 100) (fun j => if j = t then 1 else 0) =
      (if 100 = (triangleEdges t).1 then 1 else 0) -
      (if 100 = (triangleEdges t).2.1 then 1 else 0) +
      (if 100 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_101 : ∀ t : Fin 270,
    rowEval (d2Row 101) (fun j => if j = t then 1 else 0) =
      (if 101 = (triangleEdges t).1 then 1 else 0) -
      (if 101 = (triangleEdges t).2.1 then 1 else 0) +
      (if 101 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_102 : ∀ t : Fin 270,
    rowEval (d2Row 102) (fun j => if j = t then 1 else 0) =
      (if 102 = (triangleEdges t).1 then 1 else 0) -
      (if 102 = (triangleEdges t).2.1 then 1 else 0) +
      (if 102 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_103 : ∀ t : Fin 270,
    rowEval (d2Row 103) (fun j => if j = t then 1 else 0) =
      (if 103 = (triangleEdges t).1 then 1 else 0) -
      (if 103 = (triangleEdges t).2.1 then 1 else 0) +
      (if 103 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_104 : ∀ t : Fin 270,
    rowEval (d2Row 104) (fun j => if j = t then 1 else 0) =
      (if 104 = (triangleEdges t).1 then 1 else 0) -
      (if 104 = (triangleEdges t).2.1 then 1 else 0) +
      (if 104 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_105 : ∀ t : Fin 270,
    rowEval (d2Row 105) (fun j => if j = t then 1 else 0) =
      (if 105 = (triangleEdges t).1 then 1 else 0) -
      (if 105 = (triangleEdges t).2.1 then 1 else 0) +
      (if 105 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_106 : ∀ t : Fin 270,
    rowEval (d2Row 106) (fun j => if j = t then 1 else 0) =
      (if 106 = (triangleEdges t).1 then 1 else 0) -
      (if 106 = (triangleEdges t).2.1 then 1 else 0) +
      (if 106 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_107 : ∀ t : Fin 270,
    rowEval (d2Row 107) (fun j => if j = t then 1 else 0) =
      (if 107 = (triangleEdges t).1 then 1 else 0) -
      (if 107 = (triangleEdges t).2.1 then 1 else 0) +
      (if 107 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_108 : ∀ t : Fin 270,
    rowEval (d2Row 108) (fun j => if j = t then 1 else 0) =
      (if 108 = (triangleEdges t).1 then 1 else 0) -
      (if 108 = (triangleEdges t).2.1 then 1 else 0) +
      (if 108 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_109 : ∀ t : Fin 270,
    rowEval (d2Row 109) (fun j => if j = t then 1 else 0) =
      (if 109 = (triangleEdges t).1 then 1 else 0) -
      (if 109 = (triangleEdges t).2.1 then 1 else 0) +
      (if 109 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_110 : ∀ t : Fin 270,
    rowEval (d2Row 110) (fun j => if j = t then 1 else 0) =
      (if 110 = (triangleEdges t).1 then 1 else 0) -
      (if 110 = (triangleEdges t).2.1 then 1 else 0) +
      (if 110 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_111 : ∀ t : Fin 270,
    rowEval (d2Row 111) (fun j => if j = t then 1 else 0) =
      (if 111 = (triangleEdges t).1 then 1 else 0) -
      (if 111 = (triangleEdges t).2.1 then 1 else 0) +
      (if 111 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_112 : ∀ t : Fin 270,
    rowEval (d2Row 112) (fun j => if j = t then 1 else 0) =
      (if 112 = (triangleEdges t).1 then 1 else 0) -
      (if 112 = (triangleEdges t).2.1 then 1 else 0) +
      (if 112 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_113 : ∀ t : Fin 270,
    rowEval (d2Row 113) (fun j => if j = t then 1 else 0) =
      (if 113 = (triangleEdges t).1 then 1 else 0) -
      (if 113 = (triangleEdges t).2.1 then 1 else 0) +
      (if 113 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_114 : ∀ t : Fin 270,
    rowEval (d2Row 114) (fun j => if j = t then 1 else 0) =
      (if 114 = (triangleEdges t).1 then 1 else 0) -
      (if 114 = (triangleEdges t).2.1 then 1 else 0) +
      (if 114 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_115 : ∀ t : Fin 270,
    rowEval (d2Row 115) (fun j => if j = t then 1 else 0) =
      (if 115 = (triangleEdges t).1 then 1 else 0) -
      (if 115 = (triangleEdges t).2.1 then 1 else 0) +
      (if 115 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_116 : ∀ t : Fin 270,
    rowEval (d2Row 116) (fun j => if j = t then 1 else 0) =
      (if 116 = (triangleEdges t).1 then 1 else 0) -
      (if 116 = (triangleEdges t).2.1 then 1 else 0) +
      (if 116 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_117 : ∀ t : Fin 270,
    rowEval (d2Row 117) (fun j => if j = t then 1 else 0) =
      (if 117 = (triangleEdges t).1 then 1 else 0) -
      (if 117 = (triangleEdges t).2.1 then 1 else 0) +
      (if 117 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_118 : ∀ t : Fin 270,
    rowEval (d2Row 118) (fun j => if j = t then 1 else 0) =
      (if 118 = (triangleEdges t).1 then 1 else 0) -
      (if 118 = (triangleEdges t).2.1 then 1 else 0) +
      (if 118 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_119 : ∀ t : Fin 270,
    rowEval (d2Row 119) (fun j => if j = t then 1 else 0) =
      (if 119 = (triangleEdges t).1 then 1 else 0) -
      (if 119 = (triangleEdges t).2.1 then 1 else 0) +
      (if 119 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_3_oai (e : Fin 372) (hb : 90 ≤ e.val ∧ e.val < 120) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_90 t
  · exact d2_basis_cert_91 t
  · exact d2_basis_cert_92 t
  · exact d2_basis_cert_93 t
  · exact d2_basis_cert_94 t
  · exact d2_basis_cert_95 t
  · exact d2_basis_cert_96 t
  · exact d2_basis_cert_97 t
  · exact d2_basis_cert_98 t
  · exact d2_basis_cert_99 t
  · exact d2_basis_cert_100 t
  · exact d2_basis_cert_101 t
  · exact d2_basis_cert_102 t
  · exact d2_basis_cert_103 t
  · exact d2_basis_cert_104 t
  · exact d2_basis_cert_105 t
  · exact d2_basis_cert_106 t
  · exact d2_basis_cert_107 t
  · exact d2_basis_cert_108 t
  · exact d2_basis_cert_109 t
  · exact d2_basis_cert_110 t
  · exact d2_basis_cert_111 t
  · exact d2_basis_cert_112 t
  · exact d2_basis_cert_113 t
  · exact d2_basis_cert_114 t
  · exact d2_basis_cert_115 t
  · exact d2_basis_cert_116 t
  · exact d2_basis_cert_117 t
  · exact d2_basis_cert_118 t
  · exact d2_basis_cert_119 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_3_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_3_oai
