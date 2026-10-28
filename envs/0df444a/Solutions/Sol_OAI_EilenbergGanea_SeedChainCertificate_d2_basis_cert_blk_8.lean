-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:23:12.525244+00:00
-- url     : https://prove2.me/submissions/0d96f12d-71b4-4e97-8f6e-4e8be2e72840

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

theorem d2_basis_cert_240 : ∀ t : Fin 270,
    rowEval (d2Row 240) (fun j => if j = t then 1 else 0) =
      (if 240 = (triangleEdges t).1 then 1 else 0) -
      (if 240 = (triangleEdges t).2.1 then 1 else 0) +
      (if 240 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_241 : ∀ t : Fin 270,
    rowEval (d2Row 241) (fun j => if j = t then 1 else 0) =
      (if 241 = (triangleEdges t).1 then 1 else 0) -
      (if 241 = (triangleEdges t).2.1 then 1 else 0) +
      (if 241 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_242 : ∀ t : Fin 270,
    rowEval (d2Row 242) (fun j => if j = t then 1 else 0) =
      (if 242 = (triangleEdges t).1 then 1 else 0) -
      (if 242 = (triangleEdges t).2.1 then 1 else 0) +
      (if 242 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_243 : ∀ t : Fin 270,
    rowEval (d2Row 243) (fun j => if j = t then 1 else 0) =
      (if 243 = (triangleEdges t).1 then 1 else 0) -
      (if 243 = (triangleEdges t).2.1 then 1 else 0) +
      (if 243 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_244 : ∀ t : Fin 270,
    rowEval (d2Row 244) (fun j => if j = t then 1 else 0) =
      (if 244 = (triangleEdges t).1 then 1 else 0) -
      (if 244 = (triangleEdges t).2.1 then 1 else 0) +
      (if 244 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_245 : ∀ t : Fin 270,
    rowEval (d2Row 245) (fun j => if j = t then 1 else 0) =
      (if 245 = (triangleEdges t).1 then 1 else 0) -
      (if 245 = (triangleEdges t).2.1 then 1 else 0) +
      (if 245 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_246 : ∀ t : Fin 270,
    rowEval (d2Row 246) (fun j => if j = t then 1 else 0) =
      (if 246 = (triangleEdges t).1 then 1 else 0) -
      (if 246 = (triangleEdges t).2.1 then 1 else 0) +
      (if 246 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_247 : ∀ t : Fin 270,
    rowEval (d2Row 247) (fun j => if j = t then 1 else 0) =
      (if 247 = (triangleEdges t).1 then 1 else 0) -
      (if 247 = (triangleEdges t).2.1 then 1 else 0) +
      (if 247 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_248 : ∀ t : Fin 270,
    rowEval (d2Row 248) (fun j => if j = t then 1 else 0) =
      (if 248 = (triangleEdges t).1 then 1 else 0) -
      (if 248 = (triangleEdges t).2.1 then 1 else 0) +
      (if 248 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_249 : ∀ t : Fin 270,
    rowEval (d2Row 249) (fun j => if j = t then 1 else 0) =
      (if 249 = (triangleEdges t).1 then 1 else 0) -
      (if 249 = (triangleEdges t).2.1 then 1 else 0) +
      (if 249 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_250 : ∀ t : Fin 270,
    rowEval (d2Row 250) (fun j => if j = t then 1 else 0) =
      (if 250 = (triangleEdges t).1 then 1 else 0) -
      (if 250 = (triangleEdges t).2.1 then 1 else 0) +
      (if 250 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_251 : ∀ t : Fin 270,
    rowEval (d2Row 251) (fun j => if j = t then 1 else 0) =
      (if 251 = (triangleEdges t).1 then 1 else 0) -
      (if 251 = (triangleEdges t).2.1 then 1 else 0) +
      (if 251 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_252 : ∀ t : Fin 270,
    rowEval (d2Row 252) (fun j => if j = t then 1 else 0) =
      (if 252 = (triangleEdges t).1 then 1 else 0) -
      (if 252 = (triangleEdges t).2.1 then 1 else 0) +
      (if 252 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_253 : ∀ t : Fin 270,
    rowEval (d2Row 253) (fun j => if j = t then 1 else 0) =
      (if 253 = (triangleEdges t).1 then 1 else 0) -
      (if 253 = (triangleEdges t).2.1 then 1 else 0) +
      (if 253 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_254 : ∀ t : Fin 270,
    rowEval (d2Row 254) (fun j => if j = t then 1 else 0) =
      (if 254 = (triangleEdges t).1 then 1 else 0) -
      (if 254 = (triangleEdges t).2.1 then 1 else 0) +
      (if 254 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_255 : ∀ t : Fin 270,
    rowEval (d2Row 255) (fun j => if j = t then 1 else 0) =
      (if 255 = (triangleEdges t).1 then 1 else 0) -
      (if 255 = (triangleEdges t).2.1 then 1 else 0) +
      (if 255 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_256 : ∀ t : Fin 270,
    rowEval (d2Row 256) (fun j => if j = t then 1 else 0) =
      (if 256 = (triangleEdges t).1 then 1 else 0) -
      (if 256 = (triangleEdges t).2.1 then 1 else 0) +
      (if 256 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_257 : ∀ t : Fin 270,
    rowEval (d2Row 257) (fun j => if j = t then 1 else 0) =
      (if 257 = (triangleEdges t).1 then 1 else 0) -
      (if 257 = (triangleEdges t).2.1 then 1 else 0) +
      (if 257 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_258 : ∀ t : Fin 270,
    rowEval (d2Row 258) (fun j => if j = t then 1 else 0) =
      (if 258 = (triangleEdges t).1 then 1 else 0) -
      (if 258 = (triangleEdges t).2.1 then 1 else 0) +
      (if 258 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_259 : ∀ t : Fin 270,
    rowEval (d2Row 259) (fun j => if j = t then 1 else 0) =
      (if 259 = (triangleEdges t).1 then 1 else 0) -
      (if 259 = (triangleEdges t).2.1 then 1 else 0) +
      (if 259 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_260 : ∀ t : Fin 270,
    rowEval (d2Row 260) (fun j => if j = t then 1 else 0) =
      (if 260 = (triangleEdges t).1 then 1 else 0) -
      (if 260 = (triangleEdges t).2.1 then 1 else 0) +
      (if 260 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_261 : ∀ t : Fin 270,
    rowEval (d2Row 261) (fun j => if j = t then 1 else 0) =
      (if 261 = (triangleEdges t).1 then 1 else 0) -
      (if 261 = (triangleEdges t).2.1 then 1 else 0) +
      (if 261 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_262 : ∀ t : Fin 270,
    rowEval (d2Row 262) (fun j => if j = t then 1 else 0) =
      (if 262 = (triangleEdges t).1 then 1 else 0) -
      (if 262 = (triangleEdges t).2.1 then 1 else 0) +
      (if 262 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_263 : ∀ t : Fin 270,
    rowEval (d2Row 263) (fun j => if j = t then 1 else 0) =
      (if 263 = (triangleEdges t).1 then 1 else 0) -
      (if 263 = (triangleEdges t).2.1 then 1 else 0) +
      (if 263 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_264 : ∀ t : Fin 270,
    rowEval (d2Row 264) (fun j => if j = t then 1 else 0) =
      (if 264 = (triangleEdges t).1 then 1 else 0) -
      (if 264 = (triangleEdges t).2.1 then 1 else 0) +
      (if 264 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_265 : ∀ t : Fin 270,
    rowEval (d2Row 265) (fun j => if j = t then 1 else 0) =
      (if 265 = (triangleEdges t).1 then 1 else 0) -
      (if 265 = (triangleEdges t).2.1 then 1 else 0) +
      (if 265 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_266 : ∀ t : Fin 270,
    rowEval (d2Row 266) (fun j => if j = t then 1 else 0) =
      (if 266 = (triangleEdges t).1 then 1 else 0) -
      (if 266 = (triangleEdges t).2.1 then 1 else 0) +
      (if 266 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_267 : ∀ t : Fin 270,
    rowEval (d2Row 267) (fun j => if j = t then 1 else 0) =
      (if 267 = (triangleEdges t).1 then 1 else 0) -
      (if 267 = (triangleEdges t).2.1 then 1 else 0) +
      (if 267 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_268 : ∀ t : Fin 270,
    rowEval (d2Row 268) (fun j => if j = t then 1 else 0) =
      (if 268 = (triangleEdges t).1 then 1 else 0) -
      (if 268 = (triangleEdges t).2.1 then 1 else 0) +
      (if 268 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_269 : ∀ t : Fin 270,
    rowEval (d2Row 269) (fun j => if j = t then 1 else 0) =
      (if 269 = (triangleEdges t).1 then 1 else 0) -
      (if 269 = (triangleEdges t).2.1 then 1 else 0) +
      (if 269 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_8_oai (e : Fin 372) (hb : 240 ≤ e.val ∧ e.val < 270) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_240 t
  · exact d2_basis_cert_241 t
  · exact d2_basis_cert_242 t
  · exact d2_basis_cert_243 t
  · exact d2_basis_cert_244 t
  · exact d2_basis_cert_245 t
  · exact d2_basis_cert_246 t
  · exact d2_basis_cert_247 t
  · exact d2_basis_cert_248 t
  · exact d2_basis_cert_249 t
  · exact d2_basis_cert_250 t
  · exact d2_basis_cert_251 t
  · exact d2_basis_cert_252 t
  · exact d2_basis_cert_253 t
  · exact d2_basis_cert_254 t
  · exact d2_basis_cert_255 t
  · exact d2_basis_cert_256 t
  · exact d2_basis_cert_257 t
  · exact d2_basis_cert_258 t
  · exact d2_basis_cert_259 t
  · exact d2_basis_cert_260 t
  · exact d2_basis_cert_261 t
  · exact d2_basis_cert_262 t
  · exact d2_basis_cert_263 t
  · exact d2_basis_cert_264 t
  · exact d2_basis_cert_265 t
  · exact d2_basis_cert_266 t
  · exact d2_basis_cert_267 t
  · exact d2_basis_cert_268 t
  · exact d2_basis_cert_269 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_8_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_8_oai
