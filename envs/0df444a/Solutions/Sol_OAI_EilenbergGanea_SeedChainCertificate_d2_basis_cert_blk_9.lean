-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:23:56.051916+00:00
-- url     : https://prove2.me/submissions/74e17413-5595-4234-b1a0-80a8644fe7b8

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

theorem d2_basis_cert_270 : ∀ t : Fin 270,
    rowEval (d2Row 270) (fun j => if j = t then 1 else 0) =
      (if 270 = (triangleEdges t).1 then 1 else 0) -
      (if 270 = (triangleEdges t).2.1 then 1 else 0) +
      (if 270 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_271 : ∀ t : Fin 270,
    rowEval (d2Row 271) (fun j => if j = t then 1 else 0) =
      (if 271 = (triangleEdges t).1 then 1 else 0) -
      (if 271 = (triangleEdges t).2.1 then 1 else 0) +
      (if 271 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_272 : ∀ t : Fin 270,
    rowEval (d2Row 272) (fun j => if j = t then 1 else 0) =
      (if 272 = (triangleEdges t).1 then 1 else 0) -
      (if 272 = (triangleEdges t).2.1 then 1 else 0) +
      (if 272 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_273 : ∀ t : Fin 270,
    rowEval (d2Row 273) (fun j => if j = t then 1 else 0) =
      (if 273 = (triangleEdges t).1 then 1 else 0) -
      (if 273 = (triangleEdges t).2.1 then 1 else 0) +
      (if 273 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_274 : ∀ t : Fin 270,
    rowEval (d2Row 274) (fun j => if j = t then 1 else 0) =
      (if 274 = (triangleEdges t).1 then 1 else 0) -
      (if 274 = (triangleEdges t).2.1 then 1 else 0) +
      (if 274 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_275 : ∀ t : Fin 270,
    rowEval (d2Row 275) (fun j => if j = t then 1 else 0) =
      (if 275 = (triangleEdges t).1 then 1 else 0) -
      (if 275 = (triangleEdges t).2.1 then 1 else 0) +
      (if 275 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_276 : ∀ t : Fin 270,
    rowEval (d2Row 276) (fun j => if j = t then 1 else 0) =
      (if 276 = (triangleEdges t).1 then 1 else 0) -
      (if 276 = (triangleEdges t).2.1 then 1 else 0) +
      (if 276 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_277 : ∀ t : Fin 270,
    rowEval (d2Row 277) (fun j => if j = t then 1 else 0) =
      (if 277 = (triangleEdges t).1 then 1 else 0) -
      (if 277 = (triangleEdges t).2.1 then 1 else 0) +
      (if 277 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_278 : ∀ t : Fin 270,
    rowEval (d2Row 278) (fun j => if j = t then 1 else 0) =
      (if 278 = (triangleEdges t).1 then 1 else 0) -
      (if 278 = (triangleEdges t).2.1 then 1 else 0) +
      (if 278 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_279 : ∀ t : Fin 270,
    rowEval (d2Row 279) (fun j => if j = t then 1 else 0) =
      (if 279 = (triangleEdges t).1 then 1 else 0) -
      (if 279 = (triangleEdges t).2.1 then 1 else 0) +
      (if 279 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_280 : ∀ t : Fin 270,
    rowEval (d2Row 280) (fun j => if j = t then 1 else 0) =
      (if 280 = (triangleEdges t).1 then 1 else 0) -
      (if 280 = (triangleEdges t).2.1 then 1 else 0) +
      (if 280 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_281 : ∀ t : Fin 270,
    rowEval (d2Row 281) (fun j => if j = t then 1 else 0) =
      (if 281 = (triangleEdges t).1 then 1 else 0) -
      (if 281 = (triangleEdges t).2.1 then 1 else 0) +
      (if 281 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_282 : ∀ t : Fin 270,
    rowEval (d2Row 282) (fun j => if j = t then 1 else 0) =
      (if 282 = (triangleEdges t).1 then 1 else 0) -
      (if 282 = (triangleEdges t).2.1 then 1 else 0) +
      (if 282 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_283 : ∀ t : Fin 270,
    rowEval (d2Row 283) (fun j => if j = t then 1 else 0) =
      (if 283 = (triangleEdges t).1 then 1 else 0) -
      (if 283 = (triangleEdges t).2.1 then 1 else 0) +
      (if 283 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_284 : ∀ t : Fin 270,
    rowEval (d2Row 284) (fun j => if j = t then 1 else 0) =
      (if 284 = (triangleEdges t).1 then 1 else 0) -
      (if 284 = (triangleEdges t).2.1 then 1 else 0) +
      (if 284 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_285 : ∀ t : Fin 270,
    rowEval (d2Row 285) (fun j => if j = t then 1 else 0) =
      (if 285 = (triangleEdges t).1 then 1 else 0) -
      (if 285 = (triangleEdges t).2.1 then 1 else 0) +
      (if 285 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_286 : ∀ t : Fin 270,
    rowEval (d2Row 286) (fun j => if j = t then 1 else 0) =
      (if 286 = (triangleEdges t).1 then 1 else 0) -
      (if 286 = (triangleEdges t).2.1 then 1 else 0) +
      (if 286 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_287 : ∀ t : Fin 270,
    rowEval (d2Row 287) (fun j => if j = t then 1 else 0) =
      (if 287 = (triangleEdges t).1 then 1 else 0) -
      (if 287 = (triangleEdges t).2.1 then 1 else 0) +
      (if 287 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_288 : ∀ t : Fin 270,
    rowEval (d2Row 288) (fun j => if j = t then 1 else 0) =
      (if 288 = (triangleEdges t).1 then 1 else 0) -
      (if 288 = (triangleEdges t).2.1 then 1 else 0) +
      (if 288 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_289 : ∀ t : Fin 270,
    rowEval (d2Row 289) (fun j => if j = t then 1 else 0) =
      (if 289 = (triangleEdges t).1 then 1 else 0) -
      (if 289 = (triangleEdges t).2.1 then 1 else 0) +
      (if 289 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_290 : ∀ t : Fin 270,
    rowEval (d2Row 290) (fun j => if j = t then 1 else 0) =
      (if 290 = (triangleEdges t).1 then 1 else 0) -
      (if 290 = (triangleEdges t).2.1 then 1 else 0) +
      (if 290 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_291 : ∀ t : Fin 270,
    rowEval (d2Row 291) (fun j => if j = t then 1 else 0) =
      (if 291 = (triangleEdges t).1 then 1 else 0) -
      (if 291 = (triangleEdges t).2.1 then 1 else 0) +
      (if 291 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_292 : ∀ t : Fin 270,
    rowEval (d2Row 292) (fun j => if j = t then 1 else 0) =
      (if 292 = (triangleEdges t).1 then 1 else 0) -
      (if 292 = (triangleEdges t).2.1 then 1 else 0) +
      (if 292 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_293 : ∀ t : Fin 270,
    rowEval (d2Row 293) (fun j => if j = t then 1 else 0) =
      (if 293 = (triangleEdges t).1 then 1 else 0) -
      (if 293 = (triangleEdges t).2.1 then 1 else 0) +
      (if 293 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_294 : ∀ t : Fin 270,
    rowEval (d2Row 294) (fun j => if j = t then 1 else 0) =
      (if 294 = (triangleEdges t).1 then 1 else 0) -
      (if 294 = (triangleEdges t).2.1 then 1 else 0) +
      (if 294 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_295 : ∀ t : Fin 270,
    rowEval (d2Row 295) (fun j => if j = t then 1 else 0) =
      (if 295 = (triangleEdges t).1 then 1 else 0) -
      (if 295 = (triangleEdges t).2.1 then 1 else 0) +
      (if 295 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_296 : ∀ t : Fin 270,
    rowEval (d2Row 296) (fun j => if j = t then 1 else 0) =
      (if 296 = (triangleEdges t).1 then 1 else 0) -
      (if 296 = (triangleEdges t).2.1 then 1 else 0) +
      (if 296 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_297 : ∀ t : Fin 270,
    rowEval (d2Row 297) (fun j => if j = t then 1 else 0) =
      (if 297 = (triangleEdges t).1 then 1 else 0) -
      (if 297 = (triangleEdges t).2.1 then 1 else 0) +
      (if 297 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_298 : ∀ t : Fin 270,
    rowEval (d2Row 298) (fun j => if j = t then 1 else 0) =
      (if 298 = (triangleEdges t).1 then 1 else 0) -
      (if 298 = (triangleEdges t).2.1 then 1 else 0) +
      (if 298 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_299 : ∀ t : Fin 270,
    rowEval (d2Row 299) (fun j => if j = t then 1 else 0) =
      (if 299 = (triangleEdges t).1 then 1 else 0) -
      (if 299 = (triangleEdges t).2.1 then 1 else 0) +
      (if 299 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_9_oai (e : Fin 372) (hb : 270 ≤ e.val ∧ e.val < 300) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_270 t
  · exact d2_basis_cert_271 t
  · exact d2_basis_cert_272 t
  · exact d2_basis_cert_273 t
  · exact d2_basis_cert_274 t
  · exact d2_basis_cert_275 t
  · exact d2_basis_cert_276 t
  · exact d2_basis_cert_277 t
  · exact d2_basis_cert_278 t
  · exact d2_basis_cert_279 t
  · exact d2_basis_cert_280 t
  · exact d2_basis_cert_281 t
  · exact d2_basis_cert_282 t
  · exact d2_basis_cert_283 t
  · exact d2_basis_cert_284 t
  · exact d2_basis_cert_285 t
  · exact d2_basis_cert_286 t
  · exact d2_basis_cert_287 t
  · exact d2_basis_cert_288 t
  · exact d2_basis_cert_289 t
  · exact d2_basis_cert_290 t
  · exact d2_basis_cert_291 t
  · exact d2_basis_cert_292 t
  · exact d2_basis_cert_293 t
  · exact d2_basis_cert_294 t
  · exact d2_basis_cert_295 t
  · exact d2_basis_cert_296 t
  · exact d2_basis_cert_297 t
  · exact d2_basis_cert_298 t
  · exact d2_basis_cert_299 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_9_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_9_oai
