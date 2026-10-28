-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:19:16.151218+00:00
-- url     : https://prove2.me/submissions/e35b3c8c-b305-4b96-9536-0d8954c8ddfd

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

theorem d2_basis_cert_210 : ∀ t : Fin 270,
    rowEval (d2Row 210) (fun j => if j = t then 1 else 0) =
      (if 210 = (triangleEdges t).1 then 1 else 0) -
      (if 210 = (triangleEdges t).2.1 then 1 else 0) +
      (if 210 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_211 : ∀ t : Fin 270,
    rowEval (d2Row 211) (fun j => if j = t then 1 else 0) =
      (if 211 = (triangleEdges t).1 then 1 else 0) -
      (if 211 = (triangleEdges t).2.1 then 1 else 0) +
      (if 211 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_212 : ∀ t : Fin 270,
    rowEval (d2Row 212) (fun j => if j = t then 1 else 0) =
      (if 212 = (triangleEdges t).1 then 1 else 0) -
      (if 212 = (triangleEdges t).2.1 then 1 else 0) +
      (if 212 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_213 : ∀ t : Fin 270,
    rowEval (d2Row 213) (fun j => if j = t then 1 else 0) =
      (if 213 = (triangleEdges t).1 then 1 else 0) -
      (if 213 = (triangleEdges t).2.1 then 1 else 0) +
      (if 213 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_214 : ∀ t : Fin 270,
    rowEval (d2Row 214) (fun j => if j = t then 1 else 0) =
      (if 214 = (triangleEdges t).1 then 1 else 0) -
      (if 214 = (triangleEdges t).2.1 then 1 else 0) +
      (if 214 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_215 : ∀ t : Fin 270,
    rowEval (d2Row 215) (fun j => if j = t then 1 else 0) =
      (if 215 = (triangleEdges t).1 then 1 else 0) -
      (if 215 = (triangleEdges t).2.1 then 1 else 0) +
      (if 215 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_216 : ∀ t : Fin 270,
    rowEval (d2Row 216) (fun j => if j = t then 1 else 0) =
      (if 216 = (triangleEdges t).1 then 1 else 0) -
      (if 216 = (triangleEdges t).2.1 then 1 else 0) +
      (if 216 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_217 : ∀ t : Fin 270,
    rowEval (d2Row 217) (fun j => if j = t then 1 else 0) =
      (if 217 = (triangleEdges t).1 then 1 else 0) -
      (if 217 = (triangleEdges t).2.1 then 1 else 0) +
      (if 217 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_218 : ∀ t : Fin 270,
    rowEval (d2Row 218) (fun j => if j = t then 1 else 0) =
      (if 218 = (triangleEdges t).1 then 1 else 0) -
      (if 218 = (triangleEdges t).2.1 then 1 else 0) +
      (if 218 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_219 : ∀ t : Fin 270,
    rowEval (d2Row 219) (fun j => if j = t then 1 else 0) =
      (if 219 = (triangleEdges t).1 then 1 else 0) -
      (if 219 = (triangleEdges t).2.1 then 1 else 0) +
      (if 219 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_220 : ∀ t : Fin 270,
    rowEval (d2Row 220) (fun j => if j = t then 1 else 0) =
      (if 220 = (triangleEdges t).1 then 1 else 0) -
      (if 220 = (triangleEdges t).2.1 then 1 else 0) +
      (if 220 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_221 : ∀ t : Fin 270,
    rowEval (d2Row 221) (fun j => if j = t then 1 else 0) =
      (if 221 = (triangleEdges t).1 then 1 else 0) -
      (if 221 = (triangleEdges t).2.1 then 1 else 0) +
      (if 221 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_222 : ∀ t : Fin 270,
    rowEval (d2Row 222) (fun j => if j = t then 1 else 0) =
      (if 222 = (triangleEdges t).1 then 1 else 0) -
      (if 222 = (triangleEdges t).2.1 then 1 else 0) +
      (if 222 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_223 : ∀ t : Fin 270,
    rowEval (d2Row 223) (fun j => if j = t then 1 else 0) =
      (if 223 = (triangleEdges t).1 then 1 else 0) -
      (if 223 = (triangleEdges t).2.1 then 1 else 0) +
      (if 223 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_224 : ∀ t : Fin 270,
    rowEval (d2Row 224) (fun j => if j = t then 1 else 0) =
      (if 224 = (triangleEdges t).1 then 1 else 0) -
      (if 224 = (triangleEdges t).2.1 then 1 else 0) +
      (if 224 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_225 : ∀ t : Fin 270,
    rowEval (d2Row 225) (fun j => if j = t then 1 else 0) =
      (if 225 = (triangleEdges t).1 then 1 else 0) -
      (if 225 = (triangleEdges t).2.1 then 1 else 0) +
      (if 225 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_226 : ∀ t : Fin 270,
    rowEval (d2Row 226) (fun j => if j = t then 1 else 0) =
      (if 226 = (triangleEdges t).1 then 1 else 0) -
      (if 226 = (triangleEdges t).2.1 then 1 else 0) +
      (if 226 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_227 : ∀ t : Fin 270,
    rowEval (d2Row 227) (fun j => if j = t then 1 else 0) =
      (if 227 = (triangleEdges t).1 then 1 else 0) -
      (if 227 = (triangleEdges t).2.1 then 1 else 0) +
      (if 227 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_228 : ∀ t : Fin 270,
    rowEval (d2Row 228) (fun j => if j = t then 1 else 0) =
      (if 228 = (triangleEdges t).1 then 1 else 0) -
      (if 228 = (triangleEdges t).2.1 then 1 else 0) +
      (if 228 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_229 : ∀ t : Fin 270,
    rowEval (d2Row 229) (fun j => if j = t then 1 else 0) =
      (if 229 = (triangleEdges t).1 then 1 else 0) -
      (if 229 = (triangleEdges t).2.1 then 1 else 0) +
      (if 229 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_230 : ∀ t : Fin 270,
    rowEval (d2Row 230) (fun j => if j = t then 1 else 0) =
      (if 230 = (triangleEdges t).1 then 1 else 0) -
      (if 230 = (triangleEdges t).2.1 then 1 else 0) +
      (if 230 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_231 : ∀ t : Fin 270,
    rowEval (d2Row 231) (fun j => if j = t then 1 else 0) =
      (if 231 = (triangleEdges t).1 then 1 else 0) -
      (if 231 = (triangleEdges t).2.1 then 1 else 0) +
      (if 231 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_232 : ∀ t : Fin 270,
    rowEval (d2Row 232) (fun j => if j = t then 1 else 0) =
      (if 232 = (triangleEdges t).1 then 1 else 0) -
      (if 232 = (triangleEdges t).2.1 then 1 else 0) +
      (if 232 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_233 : ∀ t : Fin 270,
    rowEval (d2Row 233) (fun j => if j = t then 1 else 0) =
      (if 233 = (triangleEdges t).1 then 1 else 0) -
      (if 233 = (triangleEdges t).2.1 then 1 else 0) +
      (if 233 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_234 : ∀ t : Fin 270,
    rowEval (d2Row 234) (fun j => if j = t then 1 else 0) =
      (if 234 = (triangleEdges t).1 then 1 else 0) -
      (if 234 = (triangleEdges t).2.1 then 1 else 0) +
      (if 234 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_235 : ∀ t : Fin 270,
    rowEval (d2Row 235) (fun j => if j = t then 1 else 0) =
      (if 235 = (triangleEdges t).1 then 1 else 0) -
      (if 235 = (triangleEdges t).2.1 then 1 else 0) +
      (if 235 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_236 : ∀ t : Fin 270,
    rowEval (d2Row 236) (fun j => if j = t then 1 else 0) =
      (if 236 = (triangleEdges t).1 then 1 else 0) -
      (if 236 = (triangleEdges t).2.1 then 1 else 0) +
      (if 236 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_237 : ∀ t : Fin 270,
    rowEval (d2Row 237) (fun j => if j = t then 1 else 0) =
      (if 237 = (triangleEdges t).1 then 1 else 0) -
      (if 237 = (triangleEdges t).2.1 then 1 else 0) +
      (if 237 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_238 : ∀ t : Fin 270,
    rowEval (d2Row 238) (fun j => if j = t then 1 else 0) =
      (if 238 = (triangleEdges t).1 then 1 else 0) -
      (if 238 = (triangleEdges t).2.1 then 1 else 0) +
      (if 238 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_239 : ∀ t : Fin 270,
    rowEval (d2Row 239) (fun j => if j = t then 1 else 0) =
      (if 239 = (triangleEdges t).1 then 1 else 0) -
      (if 239 = (triangleEdges t).2.1 then 1 else 0) +
      (if 239 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_7_oai (e : Fin 372) (hb : 210 ≤ e.val ∧ e.val < 240) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_210 t
  · exact d2_basis_cert_211 t
  · exact d2_basis_cert_212 t
  · exact d2_basis_cert_213 t
  · exact d2_basis_cert_214 t
  · exact d2_basis_cert_215 t
  · exact d2_basis_cert_216 t
  · exact d2_basis_cert_217 t
  · exact d2_basis_cert_218 t
  · exact d2_basis_cert_219 t
  · exact d2_basis_cert_220 t
  · exact d2_basis_cert_221 t
  · exact d2_basis_cert_222 t
  · exact d2_basis_cert_223 t
  · exact d2_basis_cert_224 t
  · exact d2_basis_cert_225 t
  · exact d2_basis_cert_226 t
  · exact d2_basis_cert_227 t
  · exact d2_basis_cert_228 t
  · exact d2_basis_cert_229 t
  · exact d2_basis_cert_230 t
  · exact d2_basis_cert_231 t
  · exact d2_basis_cert_232 t
  · exact d2_basis_cert_233 t
  · exact d2_basis_cert_234 t
  · exact d2_basis_cert_235 t
  · exact d2_basis_cert_236 t
  · exact d2_basis_cert_237 t
  · exact d2_basis_cert_238 t
  · exact d2_basis_cert_239 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_7_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_7_oai
