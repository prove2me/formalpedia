-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:18:30.724555+00:00
-- url     : https://prove2.me/submissions/69fe8be7-832b-4159-b1e0-af0f62641dd1

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

theorem d2_basis_cert_150 : ∀ t : Fin 270,
    rowEval (d2Row 150) (fun j => if j = t then 1 else 0) =
      (if 150 = (triangleEdges t).1 then 1 else 0) -
      (if 150 = (triangleEdges t).2.1 then 1 else 0) +
      (if 150 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_151 : ∀ t : Fin 270,
    rowEval (d2Row 151) (fun j => if j = t then 1 else 0) =
      (if 151 = (triangleEdges t).1 then 1 else 0) -
      (if 151 = (triangleEdges t).2.1 then 1 else 0) +
      (if 151 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_152 : ∀ t : Fin 270,
    rowEval (d2Row 152) (fun j => if j = t then 1 else 0) =
      (if 152 = (triangleEdges t).1 then 1 else 0) -
      (if 152 = (triangleEdges t).2.1 then 1 else 0) +
      (if 152 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_153 : ∀ t : Fin 270,
    rowEval (d2Row 153) (fun j => if j = t then 1 else 0) =
      (if 153 = (triangleEdges t).1 then 1 else 0) -
      (if 153 = (triangleEdges t).2.1 then 1 else 0) +
      (if 153 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_154 : ∀ t : Fin 270,
    rowEval (d2Row 154) (fun j => if j = t then 1 else 0) =
      (if 154 = (triangleEdges t).1 then 1 else 0) -
      (if 154 = (triangleEdges t).2.1 then 1 else 0) +
      (if 154 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_155 : ∀ t : Fin 270,
    rowEval (d2Row 155) (fun j => if j = t then 1 else 0) =
      (if 155 = (triangleEdges t).1 then 1 else 0) -
      (if 155 = (triangleEdges t).2.1 then 1 else 0) +
      (if 155 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_156 : ∀ t : Fin 270,
    rowEval (d2Row 156) (fun j => if j = t then 1 else 0) =
      (if 156 = (triangleEdges t).1 then 1 else 0) -
      (if 156 = (triangleEdges t).2.1 then 1 else 0) +
      (if 156 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_157 : ∀ t : Fin 270,
    rowEval (d2Row 157) (fun j => if j = t then 1 else 0) =
      (if 157 = (triangleEdges t).1 then 1 else 0) -
      (if 157 = (triangleEdges t).2.1 then 1 else 0) +
      (if 157 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_158 : ∀ t : Fin 270,
    rowEval (d2Row 158) (fun j => if j = t then 1 else 0) =
      (if 158 = (triangleEdges t).1 then 1 else 0) -
      (if 158 = (triangleEdges t).2.1 then 1 else 0) +
      (if 158 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_159 : ∀ t : Fin 270,
    rowEval (d2Row 159) (fun j => if j = t then 1 else 0) =
      (if 159 = (triangleEdges t).1 then 1 else 0) -
      (if 159 = (triangleEdges t).2.1 then 1 else 0) +
      (if 159 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_160 : ∀ t : Fin 270,
    rowEval (d2Row 160) (fun j => if j = t then 1 else 0) =
      (if 160 = (triangleEdges t).1 then 1 else 0) -
      (if 160 = (triangleEdges t).2.1 then 1 else 0) +
      (if 160 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_161 : ∀ t : Fin 270,
    rowEval (d2Row 161) (fun j => if j = t then 1 else 0) =
      (if 161 = (triangleEdges t).1 then 1 else 0) -
      (if 161 = (triangleEdges t).2.1 then 1 else 0) +
      (if 161 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_162 : ∀ t : Fin 270,
    rowEval (d2Row 162) (fun j => if j = t then 1 else 0) =
      (if 162 = (triangleEdges t).1 then 1 else 0) -
      (if 162 = (triangleEdges t).2.1 then 1 else 0) +
      (if 162 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_163 : ∀ t : Fin 270,
    rowEval (d2Row 163) (fun j => if j = t then 1 else 0) =
      (if 163 = (triangleEdges t).1 then 1 else 0) -
      (if 163 = (triangleEdges t).2.1 then 1 else 0) +
      (if 163 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_164 : ∀ t : Fin 270,
    rowEval (d2Row 164) (fun j => if j = t then 1 else 0) =
      (if 164 = (triangleEdges t).1 then 1 else 0) -
      (if 164 = (triangleEdges t).2.1 then 1 else 0) +
      (if 164 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_165 : ∀ t : Fin 270,
    rowEval (d2Row 165) (fun j => if j = t then 1 else 0) =
      (if 165 = (triangleEdges t).1 then 1 else 0) -
      (if 165 = (triangleEdges t).2.1 then 1 else 0) +
      (if 165 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_166 : ∀ t : Fin 270,
    rowEval (d2Row 166) (fun j => if j = t then 1 else 0) =
      (if 166 = (triangleEdges t).1 then 1 else 0) -
      (if 166 = (triangleEdges t).2.1 then 1 else 0) +
      (if 166 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_167 : ∀ t : Fin 270,
    rowEval (d2Row 167) (fun j => if j = t then 1 else 0) =
      (if 167 = (triangleEdges t).1 then 1 else 0) -
      (if 167 = (triangleEdges t).2.1 then 1 else 0) +
      (if 167 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_168 : ∀ t : Fin 270,
    rowEval (d2Row 168) (fun j => if j = t then 1 else 0) =
      (if 168 = (triangleEdges t).1 then 1 else 0) -
      (if 168 = (triangleEdges t).2.1 then 1 else 0) +
      (if 168 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_169 : ∀ t : Fin 270,
    rowEval (d2Row 169) (fun j => if j = t then 1 else 0) =
      (if 169 = (triangleEdges t).1 then 1 else 0) -
      (if 169 = (triangleEdges t).2.1 then 1 else 0) +
      (if 169 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_170 : ∀ t : Fin 270,
    rowEval (d2Row 170) (fun j => if j = t then 1 else 0) =
      (if 170 = (triangleEdges t).1 then 1 else 0) -
      (if 170 = (triangleEdges t).2.1 then 1 else 0) +
      (if 170 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_171 : ∀ t : Fin 270,
    rowEval (d2Row 171) (fun j => if j = t then 1 else 0) =
      (if 171 = (triangleEdges t).1 then 1 else 0) -
      (if 171 = (triangleEdges t).2.1 then 1 else 0) +
      (if 171 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_172 : ∀ t : Fin 270,
    rowEval (d2Row 172) (fun j => if j = t then 1 else 0) =
      (if 172 = (triangleEdges t).1 then 1 else 0) -
      (if 172 = (triangleEdges t).2.1 then 1 else 0) +
      (if 172 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_173 : ∀ t : Fin 270,
    rowEval (d2Row 173) (fun j => if j = t then 1 else 0) =
      (if 173 = (triangleEdges t).1 then 1 else 0) -
      (if 173 = (triangleEdges t).2.1 then 1 else 0) +
      (if 173 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_174 : ∀ t : Fin 270,
    rowEval (d2Row 174) (fun j => if j = t then 1 else 0) =
      (if 174 = (triangleEdges t).1 then 1 else 0) -
      (if 174 = (triangleEdges t).2.1 then 1 else 0) +
      (if 174 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_175 : ∀ t : Fin 270,
    rowEval (d2Row 175) (fun j => if j = t then 1 else 0) =
      (if 175 = (triangleEdges t).1 then 1 else 0) -
      (if 175 = (triangleEdges t).2.1 then 1 else 0) +
      (if 175 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_176 : ∀ t : Fin 270,
    rowEval (d2Row 176) (fun j => if j = t then 1 else 0) =
      (if 176 = (triangleEdges t).1 then 1 else 0) -
      (if 176 = (triangleEdges t).2.1 then 1 else 0) +
      (if 176 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_177 : ∀ t : Fin 270,
    rowEval (d2Row 177) (fun j => if j = t then 1 else 0) =
      (if 177 = (triangleEdges t).1 then 1 else 0) -
      (if 177 = (triangleEdges t).2.1 then 1 else 0) +
      (if 177 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_178 : ∀ t : Fin 270,
    rowEval (d2Row 178) (fun j => if j = t then 1 else 0) =
      (if 178 = (triangleEdges t).1 then 1 else 0) -
      (if 178 = (triangleEdges t).2.1 then 1 else 0) +
      (if 178 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_179 : ∀ t : Fin 270,
    rowEval (d2Row 179) (fun j => if j = t then 1 else 0) =
      (if 179 = (triangleEdges t).1 then 1 else 0) -
      (if 179 = (triangleEdges t).2.1 then 1 else 0) +
      (if 179 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_5_oai (e : Fin 372) (hb : 150 ≤ e.val ∧ e.val < 180) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_150 t
  · exact d2_basis_cert_151 t
  · exact d2_basis_cert_152 t
  · exact d2_basis_cert_153 t
  · exact d2_basis_cert_154 t
  · exact d2_basis_cert_155 t
  · exact d2_basis_cert_156 t
  · exact d2_basis_cert_157 t
  · exact d2_basis_cert_158 t
  · exact d2_basis_cert_159 t
  · exact d2_basis_cert_160 t
  · exact d2_basis_cert_161 t
  · exact d2_basis_cert_162 t
  · exact d2_basis_cert_163 t
  · exact d2_basis_cert_164 t
  · exact d2_basis_cert_165 t
  · exact d2_basis_cert_166 t
  · exact d2_basis_cert_167 t
  · exact d2_basis_cert_168 t
  · exact d2_basis_cert_169 t
  · exact d2_basis_cert_170 t
  · exact d2_basis_cert_171 t
  · exact d2_basis_cert_172 t
  · exact d2_basis_cert_173 t
  · exact d2_basis_cert_174 t
  · exact d2_basis_cert_175 t
  · exact d2_basis_cert_176 t
  · exact d2_basis_cert_177 t
  · exact d2_basis_cert_178 t
  · exact d2_basis_cert_179 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_5_oai
