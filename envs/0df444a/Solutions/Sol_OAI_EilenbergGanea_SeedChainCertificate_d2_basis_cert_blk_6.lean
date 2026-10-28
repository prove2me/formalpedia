-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:19:14.939649+00:00
-- url     : https://prove2.me/submissions/b67876e8-be28-46f3-9a80-ba3350aace89

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

theorem d2_basis_cert_180 : ∀ t : Fin 270,
    rowEval (d2Row 180) (fun j => if j = t then 1 else 0) =
      (if 180 = (triangleEdges t).1 then 1 else 0) -
      (if 180 = (triangleEdges t).2.1 then 1 else 0) +
      (if 180 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_181 : ∀ t : Fin 270,
    rowEval (d2Row 181) (fun j => if j = t then 1 else 0) =
      (if 181 = (triangleEdges t).1 then 1 else 0) -
      (if 181 = (triangleEdges t).2.1 then 1 else 0) +
      (if 181 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_182 : ∀ t : Fin 270,
    rowEval (d2Row 182) (fun j => if j = t then 1 else 0) =
      (if 182 = (triangleEdges t).1 then 1 else 0) -
      (if 182 = (triangleEdges t).2.1 then 1 else 0) +
      (if 182 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_183 : ∀ t : Fin 270,
    rowEval (d2Row 183) (fun j => if j = t then 1 else 0) =
      (if 183 = (triangleEdges t).1 then 1 else 0) -
      (if 183 = (triangleEdges t).2.1 then 1 else 0) +
      (if 183 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_184 : ∀ t : Fin 270,
    rowEval (d2Row 184) (fun j => if j = t then 1 else 0) =
      (if 184 = (triangleEdges t).1 then 1 else 0) -
      (if 184 = (triangleEdges t).2.1 then 1 else 0) +
      (if 184 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_185 : ∀ t : Fin 270,
    rowEval (d2Row 185) (fun j => if j = t then 1 else 0) =
      (if 185 = (triangleEdges t).1 then 1 else 0) -
      (if 185 = (triangleEdges t).2.1 then 1 else 0) +
      (if 185 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_186 : ∀ t : Fin 270,
    rowEval (d2Row 186) (fun j => if j = t then 1 else 0) =
      (if 186 = (triangleEdges t).1 then 1 else 0) -
      (if 186 = (triangleEdges t).2.1 then 1 else 0) +
      (if 186 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_187 : ∀ t : Fin 270,
    rowEval (d2Row 187) (fun j => if j = t then 1 else 0) =
      (if 187 = (triangleEdges t).1 then 1 else 0) -
      (if 187 = (triangleEdges t).2.1 then 1 else 0) +
      (if 187 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_188 : ∀ t : Fin 270,
    rowEval (d2Row 188) (fun j => if j = t then 1 else 0) =
      (if 188 = (triangleEdges t).1 then 1 else 0) -
      (if 188 = (triangleEdges t).2.1 then 1 else 0) +
      (if 188 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_189 : ∀ t : Fin 270,
    rowEval (d2Row 189) (fun j => if j = t then 1 else 0) =
      (if 189 = (triangleEdges t).1 then 1 else 0) -
      (if 189 = (triangleEdges t).2.1 then 1 else 0) +
      (if 189 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_190 : ∀ t : Fin 270,
    rowEval (d2Row 190) (fun j => if j = t then 1 else 0) =
      (if 190 = (triangleEdges t).1 then 1 else 0) -
      (if 190 = (triangleEdges t).2.1 then 1 else 0) +
      (if 190 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_191 : ∀ t : Fin 270,
    rowEval (d2Row 191) (fun j => if j = t then 1 else 0) =
      (if 191 = (triangleEdges t).1 then 1 else 0) -
      (if 191 = (triangleEdges t).2.1 then 1 else 0) +
      (if 191 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_192 : ∀ t : Fin 270,
    rowEval (d2Row 192) (fun j => if j = t then 1 else 0) =
      (if 192 = (triangleEdges t).1 then 1 else 0) -
      (if 192 = (triangleEdges t).2.1 then 1 else 0) +
      (if 192 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_193 : ∀ t : Fin 270,
    rowEval (d2Row 193) (fun j => if j = t then 1 else 0) =
      (if 193 = (triangleEdges t).1 then 1 else 0) -
      (if 193 = (triangleEdges t).2.1 then 1 else 0) +
      (if 193 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_194 : ∀ t : Fin 270,
    rowEval (d2Row 194) (fun j => if j = t then 1 else 0) =
      (if 194 = (triangleEdges t).1 then 1 else 0) -
      (if 194 = (triangleEdges t).2.1 then 1 else 0) +
      (if 194 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_195 : ∀ t : Fin 270,
    rowEval (d2Row 195) (fun j => if j = t then 1 else 0) =
      (if 195 = (triangleEdges t).1 then 1 else 0) -
      (if 195 = (triangleEdges t).2.1 then 1 else 0) +
      (if 195 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_196 : ∀ t : Fin 270,
    rowEval (d2Row 196) (fun j => if j = t then 1 else 0) =
      (if 196 = (triangleEdges t).1 then 1 else 0) -
      (if 196 = (triangleEdges t).2.1 then 1 else 0) +
      (if 196 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_197 : ∀ t : Fin 270,
    rowEval (d2Row 197) (fun j => if j = t then 1 else 0) =
      (if 197 = (triangleEdges t).1 then 1 else 0) -
      (if 197 = (triangleEdges t).2.1 then 1 else 0) +
      (if 197 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_198 : ∀ t : Fin 270,
    rowEval (d2Row 198) (fun j => if j = t then 1 else 0) =
      (if 198 = (triangleEdges t).1 then 1 else 0) -
      (if 198 = (triangleEdges t).2.1 then 1 else 0) +
      (if 198 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_199 : ∀ t : Fin 270,
    rowEval (d2Row 199) (fun j => if j = t then 1 else 0) =
      (if 199 = (triangleEdges t).1 then 1 else 0) -
      (if 199 = (triangleEdges t).2.1 then 1 else 0) +
      (if 199 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_200 : ∀ t : Fin 270,
    rowEval (d2Row 200) (fun j => if j = t then 1 else 0) =
      (if 200 = (triangleEdges t).1 then 1 else 0) -
      (if 200 = (triangleEdges t).2.1 then 1 else 0) +
      (if 200 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_201 : ∀ t : Fin 270,
    rowEval (d2Row 201) (fun j => if j = t then 1 else 0) =
      (if 201 = (triangleEdges t).1 then 1 else 0) -
      (if 201 = (triangleEdges t).2.1 then 1 else 0) +
      (if 201 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_202 : ∀ t : Fin 270,
    rowEval (d2Row 202) (fun j => if j = t then 1 else 0) =
      (if 202 = (triangleEdges t).1 then 1 else 0) -
      (if 202 = (triangleEdges t).2.1 then 1 else 0) +
      (if 202 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_203 : ∀ t : Fin 270,
    rowEval (d2Row 203) (fun j => if j = t then 1 else 0) =
      (if 203 = (triangleEdges t).1 then 1 else 0) -
      (if 203 = (triangleEdges t).2.1 then 1 else 0) +
      (if 203 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_204 : ∀ t : Fin 270,
    rowEval (d2Row 204) (fun j => if j = t then 1 else 0) =
      (if 204 = (triangleEdges t).1 then 1 else 0) -
      (if 204 = (triangleEdges t).2.1 then 1 else 0) +
      (if 204 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_205 : ∀ t : Fin 270,
    rowEval (d2Row 205) (fun j => if j = t then 1 else 0) =
      (if 205 = (triangleEdges t).1 then 1 else 0) -
      (if 205 = (triangleEdges t).2.1 then 1 else 0) +
      (if 205 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_206 : ∀ t : Fin 270,
    rowEval (d2Row 206) (fun j => if j = t then 1 else 0) =
      (if 206 = (triangleEdges t).1 then 1 else 0) -
      (if 206 = (triangleEdges t).2.1 then 1 else 0) +
      (if 206 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_207 : ∀ t : Fin 270,
    rowEval (d2Row 207) (fun j => if j = t then 1 else 0) =
      (if 207 = (triangleEdges t).1 then 1 else 0) -
      (if 207 = (triangleEdges t).2.1 then 1 else 0) +
      (if 207 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_208 : ∀ t : Fin 270,
    rowEval (d2Row 208) (fun j => if j = t then 1 else 0) =
      (if 208 = (triangleEdges t).1 then 1 else 0) -
      (if 208 = (triangleEdges t).2.1 then 1 else 0) +
      (if 208 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_209 : ∀ t : Fin 270,
    rowEval (d2Row 209) (fun j => if j = t then 1 else 0) =
      (if 209 = (triangleEdges t).1 then 1 else 0) -
      (if 209 = (triangleEdges t).2.1 then 1 else 0) +
      (if 209 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_6_oai (e : Fin 372) (hb : 180 ≤ e.val ∧ e.val < 210) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_180 t
  · exact d2_basis_cert_181 t
  · exact d2_basis_cert_182 t
  · exact d2_basis_cert_183 t
  · exact d2_basis_cert_184 t
  · exact d2_basis_cert_185 t
  · exact d2_basis_cert_186 t
  · exact d2_basis_cert_187 t
  · exact d2_basis_cert_188 t
  · exact d2_basis_cert_189 t
  · exact d2_basis_cert_190 t
  · exact d2_basis_cert_191 t
  · exact d2_basis_cert_192 t
  · exact d2_basis_cert_193 t
  · exact d2_basis_cert_194 t
  · exact d2_basis_cert_195 t
  · exact d2_basis_cert_196 t
  · exact d2_basis_cert_197 t
  · exact d2_basis_cert_198 t
  · exact d2_basis_cert_199 t
  · exact d2_basis_cert_200 t
  · exact d2_basis_cert_201 t
  · exact d2_basis_cert_202 t
  · exact d2_basis_cert_203 t
  · exact d2_basis_cert_204 t
  · exact d2_basis_cert_205 t
  · exact d2_basis_cert_206 t
  · exact d2_basis_cert_207 t
  · exact d2_basis_cert_208 t
  · exact d2_basis_cert_209 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_6_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_6_oai
