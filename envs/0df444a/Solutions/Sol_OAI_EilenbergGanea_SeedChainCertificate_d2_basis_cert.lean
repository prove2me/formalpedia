-- Prove2me | solution 1 for OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:02:24.849139+00:00
-- url     : https://prove2.me/submissions/9099eced-d9f2-4e0a-b931-a64722aa9a2b

import Mathlib
import Definitions.Def_OAIEG001
import Definitions.Def_OAIEG002
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_1
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_10
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_11
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_2
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_3
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_4
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_5
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_6
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_7
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_8
import Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_d2_basis_cert_blk_9

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

theorem d2_basis_cert_0 : ∀ t : Fin 270,
    rowEval (d2Row 0) (fun j => if j = t then 1 else 0) =
      (if 0 = (triangleEdges t).1 then 1 else 0) -
      (if 0 = (triangleEdges t).2.1 then 1 else 0) +
      (if 0 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_1 : ∀ t : Fin 270,
    rowEval (d2Row 1) (fun j => if j = t then 1 else 0) =
      (if 1 = (triangleEdges t).1 then 1 else 0) -
      (if 1 = (triangleEdges t).2.1 then 1 else 0) +
      (if 1 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_2 : ∀ t : Fin 270,
    rowEval (d2Row 2) (fun j => if j = t then 1 else 0) =
      (if 2 = (triangleEdges t).1 then 1 else 0) -
      (if 2 = (triangleEdges t).2.1 then 1 else 0) +
      (if 2 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_3 : ∀ t : Fin 270,
    rowEval (d2Row 3) (fun j => if j = t then 1 else 0) =
      (if 3 = (triangleEdges t).1 then 1 else 0) -
      (if 3 = (triangleEdges t).2.1 then 1 else 0) +
      (if 3 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_4 : ∀ t : Fin 270,
    rowEval (d2Row 4) (fun j => if j = t then 1 else 0) =
      (if 4 = (triangleEdges t).1 then 1 else 0) -
      (if 4 = (triangleEdges t).2.1 then 1 else 0) +
      (if 4 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_5 : ∀ t : Fin 270,
    rowEval (d2Row 5) (fun j => if j = t then 1 else 0) =
      (if 5 = (triangleEdges t).1 then 1 else 0) -
      (if 5 = (triangleEdges t).2.1 then 1 else 0) +
      (if 5 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_6 : ∀ t : Fin 270,
    rowEval (d2Row 6) (fun j => if j = t then 1 else 0) =
      (if 6 = (triangleEdges t).1 then 1 else 0) -
      (if 6 = (triangleEdges t).2.1 then 1 else 0) +
      (if 6 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_7 : ∀ t : Fin 270,
    rowEval (d2Row 7) (fun j => if j = t then 1 else 0) =
      (if 7 = (triangleEdges t).1 then 1 else 0) -
      (if 7 = (triangleEdges t).2.1 then 1 else 0) +
      (if 7 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_8 : ∀ t : Fin 270,
    rowEval (d2Row 8) (fun j => if j = t then 1 else 0) =
      (if 8 = (triangleEdges t).1 then 1 else 0) -
      (if 8 = (triangleEdges t).2.1 then 1 else 0) +
      (if 8 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_9 : ∀ t : Fin 270,
    rowEval (d2Row 9) (fun j => if j = t then 1 else 0) =
      (if 9 = (triangleEdges t).1 then 1 else 0) -
      (if 9 = (triangleEdges t).2.1 then 1 else 0) +
      (if 9 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_10 : ∀ t : Fin 270,
    rowEval (d2Row 10) (fun j => if j = t then 1 else 0) =
      (if 10 = (triangleEdges t).1 then 1 else 0) -
      (if 10 = (triangleEdges t).2.1 then 1 else 0) +
      (if 10 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_11 : ∀ t : Fin 270,
    rowEval (d2Row 11) (fun j => if j = t then 1 else 0) =
      (if 11 = (triangleEdges t).1 then 1 else 0) -
      (if 11 = (triangleEdges t).2.1 then 1 else 0) +
      (if 11 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_12 : ∀ t : Fin 270,
    rowEval (d2Row 12) (fun j => if j = t then 1 else 0) =
      (if 12 = (triangleEdges t).1 then 1 else 0) -
      (if 12 = (triangleEdges t).2.1 then 1 else 0) +
      (if 12 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_13 : ∀ t : Fin 270,
    rowEval (d2Row 13) (fun j => if j = t then 1 else 0) =
      (if 13 = (triangleEdges t).1 then 1 else 0) -
      (if 13 = (triangleEdges t).2.1 then 1 else 0) +
      (if 13 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_14 : ∀ t : Fin 270,
    rowEval (d2Row 14) (fun j => if j = t then 1 else 0) =
      (if 14 = (triangleEdges t).1 then 1 else 0) -
      (if 14 = (triangleEdges t).2.1 then 1 else 0) +
      (if 14 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_15 : ∀ t : Fin 270,
    rowEval (d2Row 15) (fun j => if j = t then 1 else 0) =
      (if 15 = (triangleEdges t).1 then 1 else 0) -
      (if 15 = (triangleEdges t).2.1 then 1 else 0) +
      (if 15 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_16 : ∀ t : Fin 270,
    rowEval (d2Row 16) (fun j => if j = t then 1 else 0) =
      (if 16 = (triangleEdges t).1 then 1 else 0) -
      (if 16 = (triangleEdges t).2.1 then 1 else 0) +
      (if 16 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_17 : ∀ t : Fin 270,
    rowEval (d2Row 17) (fun j => if j = t then 1 else 0) =
      (if 17 = (triangleEdges t).1 then 1 else 0) -
      (if 17 = (triangleEdges t).2.1 then 1 else 0) +
      (if 17 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_18 : ∀ t : Fin 270,
    rowEval (d2Row 18) (fun j => if j = t then 1 else 0) =
      (if 18 = (triangleEdges t).1 then 1 else 0) -
      (if 18 = (triangleEdges t).2.1 then 1 else 0) +
      (if 18 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_19 : ∀ t : Fin 270,
    rowEval (d2Row 19) (fun j => if j = t then 1 else 0) =
      (if 19 = (triangleEdges t).1 then 1 else 0) -
      (if 19 = (triangleEdges t).2.1 then 1 else 0) +
      (if 19 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_20 : ∀ t : Fin 270,
    rowEval (d2Row 20) (fun j => if j = t then 1 else 0) =
      (if 20 = (triangleEdges t).1 then 1 else 0) -
      (if 20 = (triangleEdges t).2.1 then 1 else 0) +
      (if 20 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_21 : ∀ t : Fin 270,
    rowEval (d2Row 21) (fun j => if j = t then 1 else 0) =
      (if 21 = (triangleEdges t).1 then 1 else 0) -
      (if 21 = (triangleEdges t).2.1 then 1 else 0) +
      (if 21 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_22 : ∀ t : Fin 270,
    rowEval (d2Row 22) (fun j => if j = t then 1 else 0) =
      (if 22 = (triangleEdges t).1 then 1 else 0) -
      (if 22 = (triangleEdges t).2.1 then 1 else 0) +
      (if 22 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_23 : ∀ t : Fin 270,
    rowEval (d2Row 23) (fun j => if j = t then 1 else 0) =
      (if 23 = (triangleEdges t).1 then 1 else 0) -
      (if 23 = (triangleEdges t).2.1 then 1 else 0) +
      (if 23 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_24 : ∀ t : Fin 270,
    rowEval (d2Row 24) (fun j => if j = t then 1 else 0) =
      (if 24 = (triangleEdges t).1 then 1 else 0) -
      (if 24 = (triangleEdges t).2.1 then 1 else 0) +
      (if 24 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_25 : ∀ t : Fin 270,
    rowEval (d2Row 25) (fun j => if j = t then 1 else 0) =
      (if 25 = (triangleEdges t).1 then 1 else 0) -
      (if 25 = (triangleEdges t).2.1 then 1 else 0) +
      (if 25 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_26 : ∀ t : Fin 270,
    rowEval (d2Row 26) (fun j => if j = t then 1 else 0) =
      (if 26 = (triangleEdges t).1 then 1 else 0) -
      (if 26 = (triangleEdges t).2.1 then 1 else 0) +
      (if 26 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_27 : ∀ t : Fin 270,
    rowEval (d2Row 27) (fun j => if j = t then 1 else 0) =
      (if 27 = (triangleEdges t).1 then 1 else 0) -
      (if 27 = (triangleEdges t).2.1 then 1 else 0) +
      (if 27 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_28 : ∀ t : Fin 270,
    rowEval (d2Row 28) (fun j => if j = t then 1 else 0) =
      (if 28 = (triangleEdges t).1 then 1 else 0) -
      (if 28 = (triangleEdges t).2.1 then 1 else 0) +
      (if 28 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_29 : ∀ t : Fin 270,
    rowEval (d2Row 29) (fun j => if j = t then 1 else 0) =
      (if 29 = (triangleEdges t).1 then 1 else 0) -
      (if 29 = (triangleEdges t).2.1 then 1 else 0) +
      (if 29 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_360 : ∀ t : Fin 270,
    rowEval (d2Row 360) (fun j => if j = t then 1 else 0) =
      (if 360 = (triangleEdges t).1 then 1 else 0) -
      (if 360 = (triangleEdges t).2.1 then 1 else 0) +
      (if 360 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_361 : ∀ t : Fin 270,
    rowEval (d2Row 361) (fun j => if j = t then 1 else 0) =
      (if 361 = (triangleEdges t).1 then 1 else 0) -
      (if 361 = (triangleEdges t).2.1 then 1 else 0) +
      (if 361 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_362 : ∀ t : Fin 270,
    rowEval (d2Row 362) (fun j => if j = t then 1 else 0) =
      (if 362 = (triangleEdges t).1 then 1 else 0) -
      (if 362 = (triangleEdges t).2.1 then 1 else 0) +
      (if 362 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_363 : ∀ t : Fin 270,
    rowEval (d2Row 363) (fun j => if j = t then 1 else 0) =
      (if 363 = (triangleEdges t).1 then 1 else 0) -
      (if 363 = (triangleEdges t).2.1 then 1 else 0) +
      (if 363 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_364 : ∀ t : Fin 270,
    rowEval (d2Row 364) (fun j => if j = t then 1 else 0) =
      (if 364 = (triangleEdges t).1 then 1 else 0) -
      (if 364 = (triangleEdges t).2.1 then 1 else 0) +
      (if 364 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_365 : ∀ t : Fin 270,
    rowEval (d2Row 365) (fun j => if j = t then 1 else 0) =
      (if 365 = (triangleEdges t).1 then 1 else 0) -
      (if 365 = (triangleEdges t).2.1 then 1 else 0) +
      (if 365 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_366 : ∀ t : Fin 270,
    rowEval (d2Row 366) (fun j => if j = t then 1 else 0) =
      (if 366 = (triangleEdges t).1 then 1 else 0) -
      (if 366 = (triangleEdges t).2.1 then 1 else 0) +
      (if 366 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_367 : ∀ t : Fin 270,
    rowEval (d2Row 367) (fun j => if j = t then 1 else 0) =
      (if 367 = (triangleEdges t).1 then 1 else 0) -
      (if 367 = (triangleEdges t).2.1 then 1 else 0) +
      (if 367 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_368 : ∀ t : Fin 270,
    rowEval (d2Row 368) (fun j => if j = t then 1 else 0) =
      (if 368 = (triangleEdges t).1 then 1 else 0) -
      (if 368 = (triangleEdges t).2.1 then 1 else 0) +
      (if 368 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_369 : ∀ t : Fin 270,
    rowEval (d2Row 369) (fun j => if j = t then 1 else 0) =
      (if 369 = (triangleEdges t).1 then 1 else 0) -
      (if 369 = (triangleEdges t).2.1 then 1 else 0) +
      (if 369 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_370 : ∀ t : Fin 270,
    rowEval (d2Row 370) (fun j => if j = t then 1 else 0) =
      (if 370 = (triangleEdges t).1 then 1 else 0) -
      (if 370 = (triangleEdges t).2.1 then 1 else 0) +
      (if 370 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_371 : ∀ t : Fin 270,
    rowEval (d2Row 371) (fun j => if j = t then 1 else 0) =
      (if 371 = (triangleEdges t).1 then 1 else 0) -
      (if 371 = (triangleEdges t).2.1 then 1 else 0) +
      (if 371 = (triangleEdges t).2.2 then 1 else 0) := by decide +kernel

theorem d2_basis_cert_blk_0 (e : Fin 372) (hb : 0 ≤ e.val ∧ e.val < 30) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_0 t
  · exact d2_basis_cert_1 t
  · exact d2_basis_cert_2 t
  · exact d2_basis_cert_3 t
  · exact d2_basis_cert_4 t
  · exact d2_basis_cert_5 t
  · exact d2_basis_cert_6 t
  · exact d2_basis_cert_7 t
  · exact d2_basis_cert_8 t
  · exact d2_basis_cert_9 t
  · exact d2_basis_cert_10 t
  · exact d2_basis_cert_11 t
  · exact d2_basis_cert_12 t
  · exact d2_basis_cert_13 t
  · exact d2_basis_cert_14 t
  · exact d2_basis_cert_15 t
  · exact d2_basis_cert_16 t
  · exact d2_basis_cert_17 t
  · exact d2_basis_cert_18 t
  · exact d2_basis_cert_19 t
  · exact d2_basis_cert_20 t
  · exact d2_basis_cert_21 t
  · exact d2_basis_cert_22 t
  · exact d2_basis_cert_23 t
  · exact d2_basis_cert_24 t
  · exact d2_basis_cert_25 t
  · exact d2_basis_cert_26 t
  · exact d2_basis_cert_27 t
  · exact d2_basis_cert_28 t
  · exact d2_basis_cert_29 t

theorem d2_basis_cert_blk_12 (e : Fin 372) (hb : 360 ≤ e.val ∧ e.val < 372) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  rcases e with ⟨n, hn⟩
  obtain ⟨h1, h2⟩ := hb
  dsimp only at h1 h2
  interval_cases n
  · exact d2_basis_cert_360 t
  · exact d2_basis_cert_361 t
  · exact d2_basis_cert_362 t
  · exact d2_basis_cert_363 t
  · exact d2_basis_cert_364 t
  · exact d2_basis_cert_365 t
  · exact d2_basis_cert_366 t
  · exact d2_basis_cert_367 t
  · exact d2_basis_cert_368 t
  · exact d2_basis_cert_369 t
  · exact d2_basis_cert_370 t
  · exact d2_basis_cert_371 t

theorem d2_basis_cert_oai (e : Fin 372) (t : Fin 270) :
    rowEval (d2Row e) (fun i => if i = t then 1 else 0) =
      (if e = (triangleEdges t).1 then 1 else 0) -
      (if e = (triangleEdges t).2.1 then 1 else 0) + (if e = (triangleEdges t).2.2 then 1 else 0) := by
  have hlt := e.isLt
  rcases (by omega : (0 ≤ e.val ∧ e.val < 30) ∨ (30 ≤ e.val ∧ e.val < 60) ∨ (60 ≤ e.val ∧ e.val < 90) ∨ (90 ≤ e.val ∧ e.val < 120) ∨ (120 ≤ e.val ∧ e.val < 150) ∨ (150 ≤ e.val ∧ e.val < 180) ∨ (180 ≤ e.val ∧ e.val < 210) ∨ (210 ≤ e.val ∧ e.val < 240) ∨ (240 ≤ e.val ∧ e.val < 270) ∨ (270 ≤ e.val ∧ e.val < 300) ∨ (300 ≤ e.val ∧ e.val < 330) ∨ (330 ≤ e.val ∧ e.val < 360) ∨ (360 ≤ e.val ∧ e.val < 372)) with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact d2_basis_cert_blk_0 e h t
  · exact d2_basis_cert_blk_1 e h t
  · exact d2_basis_cert_blk_2 e h t
  · exact d2_basis_cert_blk_3 e h t
  · exact d2_basis_cert_blk_4 e h t
  · exact d2_basis_cert_blk_5 e h t
  · exact d2_basis_cert_blk_6 e h t
  · exact d2_basis_cert_blk_7 e h t
  · exact d2_basis_cert_blk_8 e h t
  · exact d2_basis_cert_blk_9 e h t
  · exact d2_basis_cert_blk_10 e h t
  · exact d2_basis_cert_blk_11 e h t
  · exact d2_basis_cert_blk_12 e h t

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_oai := @OAI.EilenbergGanea.SeedChainCertificate.d2_basis_cert_oai
