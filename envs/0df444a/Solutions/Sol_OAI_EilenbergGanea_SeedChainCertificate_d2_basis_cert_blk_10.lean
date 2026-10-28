-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:13:46.383924+00:00
-- url     : https://prove2.me/submissions/ffbafbc7-57fe-4792-a6d6-2acb4cdf0241

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

theorem d2_basis_cert_300 : ∀ t : Fin 270,
    rowEval (d2Row 300) (fun j => if j = t then 1 else 0) =
      (if 300 = (triangleEdges t).1 then 1 else 0) -
      (if 300 = (triangleEdges t).2.1 then 1 else 0) +
      (if 300 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_301 : ∀ t : Fin 270,
    rowEval (d2Row 301) (fun j => if j = t then 1 else 0) =
      (if 301 = (triangleEdges t).1 then 1 else 0) -
      (if 301 = (triangleEdges t).2.1 then 1 else 0) +
      (if 301 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_302 : ∀ t : Fin 270,
    rowEval (d2Row 302) (fun j => if j = t then 1 else 0) =
      (if 302 = (triangleEdges t).1 then 1 else 0) -
      (if 302 = (triangleEdges t).2.1 then 1 else 0) +
      (if 302 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_303 : ∀ t : Fin 270,
    rowEval (d2Row 303) (fun j => if j = t then 1 else 0) =
      (if 303 = (triangleEdges t).1 then 1 else 0) -
      (if 303 = (triangleEdges t).2.1 then 1 else 0) +
      (if 303 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_304 : ∀ t : Fin 270,
    rowEval (d2Row 304) (fun j => if j = t then 1 else 0) =
      (if 304 = (triangleEdges t).1 then 1 else 0) -
      (if 304 = (triangleEdges t).2.1 then 1 else 0) +
      (if 304 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_305 : ∀ t : Fin 270,
    rowEval (d2Row 305) (fun j => if j = t then 1 else 0) =
      (if 305 = (triangleEdges t).1 then 1 else 0) -
      (if 305 = (triangleEdges t).2.1 then 1 else 0) +
      (if 305 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_306 : ∀ t : Fin 270,
    rowEval (d2Row 306) (fun j => if j = t then 1 else 0) =
      (if 306 = (triangleEdges t).1 then 1 else 0) -
      (if 306 = (triangleEdges t).2.1 then 1 else 0) +
      (if 306 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_307 : ∀ t : Fin 270,
    rowEval (d2Row 307) (fun j => if j = t then 1 else 0) =
      (if 307 = (triangleEdges t).1 then 1 else 0) -
      (if 307 = (triangleEdges t).2.1 then 1 else 0) +
      (if 307 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_308 : ∀ t : Fin 270,
    rowEval (d2Row 308) (fun j => if j = t then 1 else 0) =
      (if 308 = (triangleEdges t).1 then 1 else 0) -
      (if 308 = (triangleEdges t).2.1 then 1 else 0) +
      (if 308 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_309 : ∀ t : Fin 270,
    rowEval (d2Row 309) (fun j => if j = t then 1 else 0) =
      (if 309 = (triangleEdges t).1 then 1 else 0) -
      (if 309 = (triangleEdges t).2.1 then 1 else 0) +
      (if 309 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_310 : ∀ t : Fin 270,
    rowEval (d2Row 310) (fun j => if j = t then 1 else 0) =
      (if 310 = (triangleEdges t).1 then 1 else 0) -
      (if 310 = (triangleEdges t).2.1 then 1 else 0) +
      (if 310 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_311 : ∀ t : Fin 270,
    rowEval (d2Row 311) (fun j => if j = t then 1 else 0) =
      (if 311 = (triangleEdges t).1 then 1 else 0) -
      (if 311 = (triangleEdges t).2.1 then 1 else 0) +
      (if 311 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_312 : ∀ t : Fin 270,
    rowEval (d2Row 312) (fun j => if j = t then 1 else 0) =
      (if 312 = (triangleEdges t).1 then 1 else 0) -
      (if 312 = (triangleEdges t).2.1 then 1 else 0) +
      (if 312 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_313 : ∀ t : Fin 270,
    rowEval (d2Row 313) (fun j => if j = t then 1 else 0) =
      (if 313 = (triangleEdges t).1 then 1 else 0) -
      (if 313 = (triangleEdges t).2.1 then 1 else 0) +
      (if 313 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_314 : ∀ t : Fin 270,
    rowEval (d2Row 314) (fun j => if j = t then 1 else 0) =
      (if 314 = (triangleEdges t).1 then 1 else 0) -
      (if 314 = (triangleEdges t).2.1 then 1 else 0) +
      (if 314 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_315 : ∀ t : Fin 270,
    rowEval (d2Row 315) (fun j => if j = t then 1 else 0) =
      (if 315 = (triangleEdges t).1 then 1 else 0) -
      (if 315 = (triangleEdges t).2.1 then 1 else 0) +
      (if 315 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_316 : ∀ t : Fin 270,
    rowEval (d2Row 316) (fun j => if j = t then 1 else 0) =
      (if 316 = (triangleEdges t).1 then 1 else 0) -
      (if 316 = (triangleEdges t).2.1 then 1 else 0) +
      (if 316 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_317 : ∀ t : Fin 270,
    rowEval (d2Row 317) (fun j => if j = t then 1 else 0) =
      (if 317 = (triangleEdges t).1 then 1 else 0) -
      (if 317 = (triangleEdges t).2.1 then 1 else 0) +
      (if 317 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_318 : ∀ t : Fin 270,
    rowEval (d2Row 318) (fun j => if j = t then 1 else 0) =
      (if 318 = (triangleEdges t).1 then 1 else 0) -
      (if 318 = (triangleEdges t).2.1 then 1 else 0) +
      (if 318 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_319 : ∀ t : Fin 270,
    rowEval (d2Row 319) (fun j => if j = t then 1 else 0) =
      (if 319 = (triangleEdges t).1 then 1 else 0) -
      (if 319 = (triangleEdges t).2.1 then 1 else 0) +
      (if 319 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_320 : ∀ t : Fin 270,
    rowEval (d2Row 320) (fun j => if j = t then 1 else 0) =
      (if 320 = (triangleEdges t).1 then 1 else 0) -
      (if 320 = (triangleEdges t).2.1 then 1 else 0) +
      (if 320 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_321 : ∀ t : Fin 270,
    rowEval (d2Row 321) (fun j => if j = t then 1 else 0) =
      (if 321 = (triangleEdges t).1 then 1 else 0) -
      (if 321 = (triangleEdges t).2.1 then 1 else 0) +
      (if 321 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_322 : ∀ t : Fin 270,
    rowEval (d2Row 322) (fun j => if j = t then 1 else 0) =
      (if 322 = (triangleEdges t).1 then 1 else 0) -
      (if 322 = (triangleEdges t).2.1 then 1 else 0) +
      (if 322 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_323 : ∀ t : Fin 270,
    rowEval (d2Row 323) (fun j => if j = t then 1 else 0) =
      (if 323 = (triangleEdges t).1 then 1 else 0) -
      (if 323 = (triangleEdges t).2.1 then 1 else 0) +
      (if 323 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_324 : ∀ t : Fin 270,
    rowEval (d2Row 324) (fun j => if j = t then 1 else 0) =
      (if 324 = (triangleEdges t).1 then 1 else 0) -
      (if 324 = (triangleEdges t).2.1 then 1 else 0) +
      (if 324 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_325 : ∀ t : Fin 270,
    rowEval (d2Row 325) (fun j => if j = t then 1 else 0) =
      (if 325 = (triangleEdges t).1 then 1 else 0) -
      (if 325 = (triangleEdges t).2.1 then 1 else 0) +
      (if 325 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_326 : ∀ t : Fin 270,
    rowEval (d2Row 326) (fun j => if j = t then 1 else 0) =
      (if 326 = (triangleEdges t).1 then 1 else 0) -
      (if 326 = (triangleEdges t).2.1 then 1 else 0) +
      (if 326 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_327 : ∀ t : Fin 270,
    rowEval (d2Row 327) (fun j => if j = t then 1 else 0) =
      (if 327 = (triangleEdges t).1 then 1 else 0) -
      (if 327 = (triangleEdges t).2.1 then 1 else 0) +
      (if 327 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_328 : ∀ t : Fin 270,
    rowEval (d2Row 328) (fun j => if j = t then 1 else 0) =
      (if 328 = (triangleEdges t).1 then 1 else 0) -
      (if 328 = (triangleEdges t).2.1 then 1 else 0) +
      (if 328 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_329 : ∀ t : Fin 270,
    rowEval (d2Row 329) (fun j => if j = t then 1 else 0) =
      (if 329 = (triangleEdges t).1 then 1 else 0) -
      (if 329 = (triangleEdges t).2.1 then 1 else 0) +
      (if 329 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_10_oai (e : Fin 372) (hb : 300 ≤ e.val ∧ e.val < 330) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_300 t
  · exact d2_basis_cert_301 t
  · exact d2_basis_cert_302 t
  · exact d2_basis_cert_303 t
  · exact d2_basis_cert_304 t
  · exact d2_basis_cert_305 t
  · exact d2_basis_cert_306 t
  · exact d2_basis_cert_307 t
  · exact d2_basis_cert_308 t
  · exact d2_basis_cert_309 t
  · exact d2_basis_cert_310 t
  · exact d2_basis_cert_311 t
  · exact d2_basis_cert_312 t
  · exact d2_basis_cert_313 t
  · exact d2_basis_cert_314 t
  · exact d2_basis_cert_315 t
  · exact d2_basis_cert_316 t
  · exact d2_basis_cert_317 t
  · exact d2_basis_cert_318 t
  · exact d2_basis_cert_319 t
  · exact d2_basis_cert_320 t
  · exact d2_basis_cert_321 t
  · exact d2_basis_cert_322 t
  · exact d2_basis_cert_323 t
  · exact d2_basis_cert_324 t
  · exact d2_basis_cert_325 t
  · exact d2_basis_cert_326 t
  · exact d2_basis_cert_327 t
  · exact d2_basis_cert_328 t
  · exact d2_basis_cert_329 t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_10_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_blk_10_oai
