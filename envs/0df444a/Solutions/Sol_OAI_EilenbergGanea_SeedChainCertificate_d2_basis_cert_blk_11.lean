-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:14:09.292277+00:00
-- url     : https://prove2.me/submissions/f0683a96-63fd-48d7-b693-91d61af5b281

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

theorem d2_basis_cert_330 : ∀ t : Fin 270,
    rowEval (d2Row 330) (fun j => if j = t then 1 else 0) =
      (if 330 = (triangleEdges t).1 then 1 else 0) -
      (if 330 = (triangleEdges t).2.1 then 1 else 0) +
      (if 330 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_331 : ∀ t : Fin 270,
    rowEval (d2Row 331) (fun j => if j = t then 1 else 0) =
      (if 331 = (triangleEdges t).1 then 1 else 0) -
      (if 331 = (triangleEdges t).2.1 then 1 else 0) +
      (if 331 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_332 : ∀ t : Fin 270,
    rowEval (d2Row 332) (fun j => if j = t then 1 else 0) =
      (if 332 = (triangleEdges t).1 then 1 else 0) -
      (if 332 = (triangleEdges t).2.1 then 1 else 0) +
      (if 332 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_333 : ∀ t : Fin 270,
    rowEval (d2Row 333) (fun j => if j = t then 1 else 0) =
      (if 333 = (triangleEdges t).1 then 1 else 0) -
      (if 333 = (triangleEdges t).2.1 then 1 else 0) +
      (if 333 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_334 : ∀ t : Fin 270,
    rowEval (d2Row 334) (fun j => if j = t then 1 else 0) =
      (if 334 = (triangleEdges t).1 then 1 else 0) -
      (if 334 = (triangleEdges t).2.1 then 1 else 0) +
      (if 334 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_335 : ∀ t : Fin 270,
    rowEval (d2Row 335) (fun j => if j = t then 1 else 0) =
      (if 335 = (triangleEdges t).1 then 1 else 0) -
      (if 335 = (triangleEdges t).2.1 then 1 else 0) +
      (if 335 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_336 : ∀ t : Fin 270,
    rowEval (d2Row 336) (fun j => if j = t then 1 else 0) =
      (if 336 = (triangleEdges t).1 then 1 else 0) -
      (if 336 = (triangleEdges t).2.1 then 1 else 0) +
      (if 336 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_337 : ∀ t : Fin 270,
    rowEval (d2Row 337) (fun j => if j = t then 1 else 0) =
      (if 337 = (triangleEdges t).1 then 1 else 0) -
      (if 337 = (triangleEdges t).2.1 then 1 else 0) +
      (if 337 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_338 : ∀ t : Fin 270,
    rowEval (d2Row 338) (fun j => if j = t then 1 else 0) =
      (if 338 = (triangleEdges t).1 then 1 else 0) -
      (if 338 = (triangleEdges t).2.1 then 1 else 0) +
      (if 338 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_339 : ∀ t : Fin 270,
    rowEval (d2Row 339) (fun j => if j = t then 1 else 0) =
      (if 339 = (triangleEdges t).1 then 1 else 0) -
      (if 339 = (triangleEdges t).2.1 then 1 else 0) +
      (if 339 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_340 : ∀ t : Fin 270,
    rowEval (d2Row 340) (fun j => if j = t then 1 else 0) =
      (if 340 = (triangleEdges t).1 then 1 else 0) -
      (if 340 = (triangleEdges t).2.1 then 1 else 0) +
      (if 340 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_341 : ∀ t : Fin 270,
    rowEval (d2Row 341) (fun j => if j = t then 1 else 0) =
      (if 341 = (triangleEdges t).1 then 1 else 0) -
      (if 341 = (triangleEdges t).2.1 then 1 else 0) +
      (if 341 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_342 : ∀ t : Fin 270,
    rowEval (d2Row 342) (fun j => if j = t then 1 else 0) =
      (if 342 = (triangleEdges t).1 then 1 else 0) -
      (if 342 = (triangleEdges t).2.1 then 1 else 0) +
      (if 342 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_343 : ∀ t : Fin 270,
    rowEval (d2Row 343) (fun j => if j = t then 1 else 0) =
      (if 343 = (triangleEdges t).1 then 1 else 0) -
      (if 343 = (triangleEdges t).2.1 then 1 else 0) +
      (if 343 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_344 : ∀ t : Fin 270,
    rowEval (d2Row 344) (fun j => if j = t then 1 else 0) =
      (if 344 = (triangleEdges t).1 then 1 else 0) -
      (if 344 = (triangleEdges t).2.1 then 1 else 0) +
      (if 344 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_345 : ∀ t : Fin 270,
    rowEval (d2Row 345) (fun j => if j = t then 1 else 0) =
      (if 345 = (triangleEdges t).1 then 1 else 0) -
      (if 345 = (triangleEdges t).2.1 then 1 else 0) +
      (if 345 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_346 : ∀ t : Fin 270,
    rowEval (d2Row 346) (fun j => if j = t then 1 else 0) =
      (if 346 = (triangleEdges t).1 then 1 else 0) -
      (if 346 = (triangleEdges t).2.1 then 1 else 0) +
      (if 346 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_347 : ∀ t : Fin 270,
    rowEval (d2Row 347) (fun j => if j = t then 1 else 0) =
      (if 347 = (triangleEdges t).1 then 1 else 0) -
      (if 347 = (triangleEdges t).2.1 then 1 else 0) +
      (if 347 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_348 : ∀ t : Fin 270,
    rowEval (d2Row 348) (fun j => if j = t then 1 else 0) =
      (if 348 = (triangleEdges t).1 then 1 else 0) -
      (if 348 = (triangleEdges t).2.1 then 1 else 0) +
      (if 348 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_349 : ∀ t : Fin 270,
    rowEval (d2Row 349) (fun j => if j = t then 1 else 0) =
      (if 349 = (triangleEdges t).1 then 1 else 0) -
      (if 349 = (triangleEdges t).2.1 then 1 else 0) +
      (if 349 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_350 : ∀ t : Fin 270,
    rowEval (d2Row 350) (fun j => if j = t then 1 else 0) =
      (if 350 = (triangleEdges t).1 then 1 else 0) -
      (if 350 = (triangleEdges t).2.1 then 1 else 0) +
      (if 350 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_351 : ∀ t : Fin 270,
    rowEval (d2Row 351) (fun j => if j = t then 1 else 0) =
      (if 351 = (triangleEdges t).1 then 1 else 0) -
      (if 351 = (triangleEdges t).2.1 then 1 else 0) +
      (if 351 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_352 : ∀ t : Fin 270,
    rowEval (d2Row 352) (fun j => if j = t then 1 else 0) =
      (if 352 = (triangleEdges t).1 then 1 else 0) -
      (if 352 = (triangleEdges t).2.1 then 1 else 0) +
      (if 352 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_353 : ∀ t : Fin 270,
    rowEval (d2Row 353) (fun j => if j = t then 1 else 0) =
      (if 353 = (triangleEdges t).1 then 1 else 0) -
      (if 353 = (triangleEdges t).2.1 then 1 else 0) +
      (if 353 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_354 : ∀ t : Fin 270,
    rowEval (d2Row 354) (fun j => if j = t then 1 else 0) =
      (if 354 = (triangleEdges t).1 then 1 else 0) -
      (if 354 = (triangleEdges t).2.1 then 1 else 0) +
      (if 354 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_355 : ∀ t : Fin 270,
    rowEval (d2Row 355) (fun j => if j = t then 1 else 0) =
      (if 355 = (triangleEdges t).1 then 1 else 0) -
      (if 355 = (triangleEdges t).2.1 then 1 else 0) +
      (if 355 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_356 : ∀ t : Fin 270,
    rowEval (d2Row 356) (fun j => if j = t then 1 else 0) =
      (if 356 = (triangleEdges t).1 then 1 else 0) -
      (if 356 = (triangleEdges t).2.1 then 1 else 0) +
      (if 356 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_357 : ∀ t : Fin 270,
    rowEval (d2Row 357) (fun j => if j = t then 1 else 0) =
      (if 357 = (triangleEdges t).1 then 1 else 0) -
      (if 357 = (triangleEdges t).2.1 then 1 else 0) +
      (if 357 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_358 : ∀ t : Fin 270,
    rowEval (d2Row 358) (fun j => if j = t then 1 else 0) =
      (if 358 = (triangleEdges t).1 then 1 else 0) -
      (if 358 = (triangleEdges t).2.1 then 1 else 0) +
      (if 358 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_359 : ∀ t : Fin 270,
    rowEval (d2Row 359) (fun j => if j = t then 1 else 0) =
      (if 359 = (triangleEdges t).1 then 1 else 0) -
      (if 359 = (triangleEdges t).2.1 then 1 else 0) +
      (if 359 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_11_oai (e : Fin 372) (hb : 330 ≤ e.val ∧ e.val < 360) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_330 t
  · exact d2_basis_cert_331 t
  · exact d2_basis_cert_332 t
  · exact d2_basis_cert_333 t
  · exact d2_basis_cert_334 t
  · exact d2_basis_cert_335 t
  · exact d2_basis_cert_336 t
  · exact d2_basis_cert_337 t
  · exact d2_basis_cert_338 t
  · exact d2_basis_cert_339 t
  · exact d2_basis_cert_340 t
  · exact d2_basis_cert_341 t
  · exact d2_basis_cert_342 t
  · exact d2_basis_cert_343 t
  · exact d2_basis_cert_344 t
  · exact d2_basis_cert_345 t
  · exact d2_basis_cert_346 t
  · exact d2_basis_cert_347 t
  · exact d2_basis_cert_348 t
  · exact d2_basis_cert_349 t
  · exact d2_basis_cert_350 t
  · exact d2_basis_cert_351 t
  · exact d2_basis_cert_352 t
  · exact d2_basis_cert_353 t
  · exact d2_basis_cert_354 t
  · exact d2_basis_cert_355 t
  · exact d2_basis_cert_356 t
  · exact d2_basis_cert_357 t
  · exact d2_basis_cert_358 t
  · exact d2_basis_cert_359 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_11_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_11_oai
