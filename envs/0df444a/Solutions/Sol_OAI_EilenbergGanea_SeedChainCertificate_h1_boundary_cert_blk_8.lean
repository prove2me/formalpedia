-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:42:39.802437+00:00
-- url     : https://prove2.me/submissions/24b8286a-f454-40f1-aa9e-9ea2d108ccd5

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

theorem h1_boundary_cert_240 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 240).1 j - h1Coeff (triangleEdges 240).2.1 j +
      h1Coeff (triangleEdges 240).2.2 j = if j = 240 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_241 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 241).1 j - h1Coeff (triangleEdges 241).2.1 j +
      h1Coeff (triangleEdges 241).2.2 j = if j = 241 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_242 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 242).1 j - h1Coeff (triangleEdges 242).2.1 j +
      h1Coeff (triangleEdges 242).2.2 j = if j = 242 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_243 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 243).1 j - h1Coeff (triangleEdges 243).2.1 j +
      h1Coeff (triangleEdges 243).2.2 j = if j = 243 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_244 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 244).1 j - h1Coeff (triangleEdges 244).2.1 j +
      h1Coeff (triangleEdges 244).2.2 j = if j = 244 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_245 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 245).1 j - h1Coeff (triangleEdges 245).2.1 j +
      h1Coeff (triangleEdges 245).2.2 j = if j = 245 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_246 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 246).1 j - h1Coeff (triangleEdges 246).2.1 j +
      h1Coeff (triangleEdges 246).2.2 j = if j = 246 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_247 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 247).1 j - h1Coeff (triangleEdges 247).2.1 j +
      h1Coeff (triangleEdges 247).2.2 j = if j = 247 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_248 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 248).1 j - h1Coeff (triangleEdges 248).2.1 j +
      h1Coeff (triangleEdges 248).2.2 j = if j = 248 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_249 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 249).1 j - h1Coeff (triangleEdges 249).2.1 j +
      h1Coeff (triangleEdges 249).2.2 j = if j = 249 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_250 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 250).1 j - h1Coeff (triangleEdges 250).2.1 j +
      h1Coeff (triangleEdges 250).2.2 j = if j = 250 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_251 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 251).1 j - h1Coeff (triangleEdges 251).2.1 j +
      h1Coeff (triangleEdges 251).2.2 j = if j = 251 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_252 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 252).1 j - h1Coeff (triangleEdges 252).2.1 j +
      h1Coeff (triangleEdges 252).2.2 j = if j = 252 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_253 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 253).1 j - h1Coeff (triangleEdges 253).2.1 j +
      h1Coeff (triangleEdges 253).2.2 j = if j = 253 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_254 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 254).1 j - h1Coeff (triangleEdges 254).2.1 j +
      h1Coeff (triangleEdges 254).2.2 j = if j = 254 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_255 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 255).1 j - h1Coeff (triangleEdges 255).2.1 j +
      h1Coeff (triangleEdges 255).2.2 j = if j = 255 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_256 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 256).1 j - h1Coeff (triangleEdges 256).2.1 j +
      h1Coeff (triangleEdges 256).2.2 j = if j = 256 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_257 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 257).1 j - h1Coeff (triangleEdges 257).2.1 j +
      h1Coeff (triangleEdges 257).2.2 j = if j = 257 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_258 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 258).1 j - h1Coeff (triangleEdges 258).2.1 j +
      h1Coeff (triangleEdges 258).2.2 j = if j = 258 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_259 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 259).1 j - h1Coeff (triangleEdges 259).2.1 j +
      h1Coeff (triangleEdges 259).2.2 j = if j = 259 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_260 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 260).1 j - h1Coeff (triangleEdges 260).2.1 j +
      h1Coeff (triangleEdges 260).2.2 j = if j = 260 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_261 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 261).1 j - h1Coeff (triangleEdges 261).2.1 j +
      h1Coeff (triangleEdges 261).2.2 j = if j = 261 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_262 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 262).1 j - h1Coeff (triangleEdges 262).2.1 j +
      h1Coeff (triangleEdges 262).2.2 j = if j = 262 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_263 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 263).1 j - h1Coeff (triangleEdges 263).2.1 j +
      h1Coeff (triangleEdges 263).2.2 j = if j = 263 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_264 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 264).1 j - h1Coeff (triangleEdges 264).2.1 j +
      h1Coeff (triangleEdges 264).2.2 j = if j = 264 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_265 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 265).1 j - h1Coeff (triangleEdges 265).2.1 j +
      h1Coeff (triangleEdges 265).2.2 j = if j = 265 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_266 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 266).1 j - h1Coeff (triangleEdges 266).2.1 j +
      h1Coeff (triangleEdges 266).2.2 j = if j = 266 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_267 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 267).1 j - h1Coeff (triangleEdges 267).2.1 j +
      h1Coeff (triangleEdges 267).2.2 j = if j = 267 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_268 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 268).1 j - h1Coeff (triangleEdges 268).2.1 j +
      h1Coeff (triangleEdges 268).2.2 j = if j = 268 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_269 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 269).1 j - h1Coeff (triangleEdges 269).2.1 j +
      h1Coeff (triangleEdges 269).2.2 j = if j = 269 then 1 else 0 := by decide +kernel

theorem h1_boundary_cert_blk_8_oai (t : Fin 270) (hb : 240 ≤ t.val ∧ t.val < 270) (j : Fin 270) :
    h1Coeff (triangleEdges t).1 j - h1Coeff (triangleEdges t).2.1 j +
      h1Coeff (triangleEdges t).2.2 j = if j = t then 1 else 0 := by
  rcases t with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact h1_boundary_cert_240 j
  · exact h1_boundary_cert_241 j
  · exact h1_boundary_cert_242 j
  · exact h1_boundary_cert_243 j
  · exact h1_boundary_cert_244 j
  · exact h1_boundary_cert_245 j
  · exact h1_boundary_cert_246 j
  · exact h1_boundary_cert_247 j
  · exact h1_boundary_cert_248 j
  · exact h1_boundary_cert_249 j
  · exact h1_boundary_cert_250 j
  · exact h1_boundary_cert_251 j
  · exact h1_boundary_cert_252 j
  · exact h1_boundary_cert_253 j
  · exact h1_boundary_cert_254 j
  · exact h1_boundary_cert_255 j
  · exact h1_boundary_cert_256 j
  · exact h1_boundary_cert_257 j
  · exact h1_boundary_cert_258 j
  · exact h1_boundary_cert_259 j
  · exact h1_boundary_cert_260 j
  · exact h1_boundary_cert_261 j
  · exact h1_boundary_cert_262 j
  · exact h1_boundary_cert_263 j
  · exact h1_boundary_cert_264 j
  · exact h1_boundary_cert_265 j
  · exact h1_boundary_cert_266 j
  · exact h1_boundary_cert_267 j
  · exact h1_boundary_cert_268 j
  · exact h1_boundary_cert_269 j

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_8_oai := @OAI.EilenbergGanea.SeedChainCertificate.h1_boundary_cert_blk_8_oai
