-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.bordered_lc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:05.813887+00:00
-- url     : https://prove2.me/submissions/62986882-e6b8-41af-a989-2470d9cc5a7e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cl

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution (j : Fin n) :
    bordered M c r d (Fin.last n) j.castSucc = r j := by simp [bordered]
end GlobalTheory.CompanionTheory.HeckeMult
