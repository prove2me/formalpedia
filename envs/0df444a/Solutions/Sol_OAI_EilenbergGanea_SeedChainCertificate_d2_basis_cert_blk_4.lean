-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:18:29.709881+00:00
-- url     : https://prove2.me/submissions/3469e01e-cb37-4b4d-ae76-ba583bc9585f

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

theorem d2_basis_cert_120 : ∀ t : Fin 270,
    rowEval (d2Row 120) (fun j => if j = t then 1 else 0) =
      (if 120 = (triangleEdges t).1 then 1 else 0) -
      (if 120 = (triangleEdges t).2.1 then 1 else 0) +
      (if 120 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_121 : ∀ t : Fin 270,
    rowEval (d2Row 121) (fun j => if j = t then 1 else 0) =
      (if 121 = (triangleEdges t).1 then 1 else 0) -
      (if 121 = (triangleEdges t).2.1 then 1 else 0) +
      (if 121 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_122 : ∀ t : Fin 270,
    rowEval (d2Row 122) (fun j => if j = t then 1 else 0) =
      (if 122 = (triangleEdges t).1 then 1 else 0) -
      (if 122 = (triangleEdges t).2.1 then 1 else 0) +
      (if 122 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_123 : ∀ t : Fin 270,
    rowEval (d2Row 123) (fun j => if j = t then 1 else 0) =
      (if 123 = (triangleEdges t).1 then 1 else 0) -
      (if 123 = (triangleEdges t).2.1 then 1 else 0) +
      (if 123 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_124 : ∀ t : Fin 270,
    rowEval (d2Row 124) (fun j => if j = t then 1 else 0) =
      (if 124 = (triangleEdges t).1 then 1 else 0) -
      (if 124 = (triangleEdges t).2.1 then 1 else 0) +
      (if 124 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_125 : ∀ t : Fin 270,
    rowEval (d2Row 125) (fun j => if j = t then 1 else 0) =
      (if 125 = (triangleEdges t).1 then 1 else 0) -
      (if 125 = (triangleEdges t).2.1 then 1 else 0) +
      (if 125 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_126 : ∀ t : Fin 270,
    rowEval (d2Row 126) (fun j => if j = t then 1 else 0) =
      (if 126 = (triangleEdges t).1 then 1 else 0) -
      (if 126 = (triangleEdges t).2.1 then 1 else 0) +
      (if 126 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_127 : ∀ t : Fin 270,
    rowEval (d2Row 127) (fun j => if j = t then 1 else 0) =
      (if 127 = (triangleEdges t).1 then 1 else 0) -
      (if 127 = (triangleEdges t).2.1 then 1 else 0) +
      (if 127 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_128 : ∀ t : Fin 270,
    rowEval (d2Row 128) (fun j => if j = t then 1 else 0) =
      (if 128 = (triangleEdges t).1 then 1 else 0) -
      (if 128 = (triangleEdges t).2.1 then 1 else 0) +
      (if 128 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_129 : ∀ t : Fin 270,
    rowEval (d2Row 129) (fun j => if j = t then 1 else 0) =
      (if 129 = (triangleEdges t).1 then 1 else 0) -
      (if 129 = (triangleEdges t).2.1 then 1 else 0) +
      (if 129 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_130 : ∀ t : Fin 270,
    rowEval (d2Row 130) (fun j => if j = t then 1 else 0) =
      (if 130 = (triangleEdges t).1 then 1 else 0) -
      (if 130 = (triangleEdges t).2.1 then 1 else 0) +
      (if 130 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_131 : ∀ t : Fin 270,
    rowEval (d2Row 131) (fun j => if j = t then 1 else 0) =
      (if 131 = (triangleEdges t).1 then 1 else 0) -
      (if 131 = (triangleEdges t).2.1 then 1 else 0) +
      (if 131 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_132 : ∀ t : Fin 270,
    rowEval (d2Row 132) (fun j => if j = t then 1 else 0) =
      (if 132 = (triangleEdges t).1 then 1 else 0) -
      (if 132 = (triangleEdges t).2.1 then 1 else 0) +
      (if 132 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_133 : ∀ t : Fin 270,
    rowEval (d2Row 133) (fun j => if j = t then 1 else 0) =
      (if 133 = (triangleEdges t).1 then 1 else 0) -
      (if 133 = (triangleEdges t).2.1 then 1 else 0) +
      (if 133 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_134 : ∀ t : Fin 270,
    rowEval (d2Row 134) (fun j => if j = t then 1 else 0) =
      (if 134 = (triangleEdges t).1 then 1 else 0) -
      (if 134 = (triangleEdges t).2.1 then 1 else 0) +
      (if 134 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_135 : ∀ t : Fin 270,
    rowEval (d2Row 135) (fun j => if j = t then 1 else 0) =
      (if 135 = (triangleEdges t).1 then 1 else 0) -
      (if 135 = (triangleEdges t).2.1 then 1 else 0) +
      (if 135 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_136 : ∀ t : Fin 270,
    rowEval (d2Row 136) (fun j => if j = t then 1 else 0) =
      (if 136 = (triangleEdges t).1 then 1 else 0) -
      (if 136 = (triangleEdges t).2.1 then 1 else 0) +
      (if 136 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_137 : ∀ t : Fin 270,
    rowEval (d2Row 137) (fun j => if j = t then 1 else 0) =
      (if 137 = (triangleEdges t).1 then 1 else 0) -
      (if 137 = (triangleEdges t).2.1 then 1 else 0) +
      (if 137 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_138 : ∀ t : Fin 270,
    rowEval (d2Row 138) (fun j => if j = t then 1 else 0) =
      (if 138 = (triangleEdges t).1 then 1 else 0) -
      (if 138 = (triangleEdges t).2.1 then 1 else 0) +
      (if 138 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_139 : ∀ t : Fin 270,
    rowEval (d2Row 139) (fun j => if j = t then 1 else 0) =
      (if 139 = (triangleEdges t).1 then 1 else 0) -
      (if 139 = (triangleEdges t).2.1 then 1 else 0) +
      (if 139 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_140 : ∀ t : Fin 270,
    rowEval (d2Row 140) (fun j => if j = t then 1 else 0) =
      (if 140 = (triangleEdges t).1 then 1 else 0) -
      (if 140 = (triangleEdges t).2.1 then 1 else 0) +
      (if 140 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_141 : ∀ t : Fin 270,
    rowEval (d2Row 141) (fun j => if j = t then 1 else 0) =
      (if 141 = (triangleEdges t).1 then 1 else 0) -
      (if 141 = (triangleEdges t).2.1 then 1 else 0) +
      (if 141 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_142 : ∀ t : Fin 270,
    rowEval (d2Row 142) (fun j => if j = t then 1 else 0) =
      (if 142 = (triangleEdges t).1 then 1 else 0) -
      (if 142 = (triangleEdges t).2.1 then 1 else 0) +
      (if 142 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_143 : ∀ t : Fin 270,
    rowEval (d2Row 143) (fun j => if j = t then 1 else 0) =
      (if 143 = (triangleEdges t).1 then 1 else 0) -
      (if 143 = (triangleEdges t).2.1 then 1 else 0) +
      (if 143 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_144 : ∀ t : Fin 270,
    rowEval (d2Row 144) (fun j => if j = t then 1 else 0) =
      (if 144 = (triangleEdges t).1 then 1 else 0) -
      (if 144 = (triangleEdges t).2.1 then 1 else 0) +
      (if 144 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_145 : ∀ t : Fin 270,
    rowEval (d2Row 145) (fun j => if j = t then 1 else 0) =
      (if 145 = (triangleEdges t).1 then 1 else 0) -
      (if 145 = (triangleEdges t).2.1 then 1 else 0) +
      (if 145 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_146 : ∀ t : Fin 270,
    rowEval (d2Row 146) (fun j => if j = t then 1 else 0) =
      (if 146 = (triangleEdges t).1 then 1 else 0) -
      (if 146 = (triangleEdges t).2.1 then 1 else 0) +
      (if 146 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_147 : ∀ t : Fin 270,
    rowEval (d2Row 147) (fun j => if j = t then 1 else 0) =
      (if 147 = (triangleEdges t).1 then 1 else 0) -
      (if 147 = (triangleEdges t).2.1 then 1 else 0) +
      (if 147 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_148 : ∀ t : Fin 270,
    rowEval (d2Row 148) (fun j => if j = t then 1 else 0) =
      (if 148 = (triangleEdges t).1 then 1 else 0) -
      (if 148 = (triangleEdges t).2.1 then 1 else 0) +
      (if 148 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_149 : ∀ t : Fin 270,
    rowEval (d2Row 149) (fun j => if j = t then 1 else 0) =
      (if 149 = (triangleEdges t).1 then 1 else 0) -
      (if 149 = (triangleEdges t).2.1 then 1 else 0) +
      (if 149 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_4_oai (e : Fin 372) (hb : 120 ≤ e.val ∧ e.val < 150) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_120 t
  · exact d2_basis_cert_121 t
  · exact d2_basis_cert_122 t
  · exact d2_basis_cert_123 t
  · exact d2_basis_cert_124 t
  · exact d2_basis_cert_125 t
  · exact d2_basis_cert_126 t
  · exact d2_basis_cert_127 t
  · exact d2_basis_cert_128 t
  · exact d2_basis_cert_129 t
  · exact d2_basis_cert_130 t
  · exact d2_basis_cert_131 t
  · exact d2_basis_cert_132 t
  · exact d2_basis_cert_133 t
  · exact d2_basis_cert_134 t
  · exact d2_basis_cert_135 t
  · exact d2_basis_cert_136 t
  · exact d2_basis_cert_137 t
  · exact d2_basis_cert_138 t
  · exact d2_basis_cert_139 t
  · exact d2_basis_cert_140 t
  · exact d2_basis_cert_141 t
  · exact d2_basis_cert_142 t
  · exact d2_basis_cert_143 t
  · exact d2_basis_cert_144 t
  · exact d2_basis_cert_145 t
  · exact d2_basis_cert_146 t
  · exact d2_basis_cert_147 t
  · exact d2_basis_cert_148 t
  · exact d2_basis_cert_149 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_4_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_4_oai
