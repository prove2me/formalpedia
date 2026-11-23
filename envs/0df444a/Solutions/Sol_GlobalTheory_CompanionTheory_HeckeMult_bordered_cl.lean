-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.bordered_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:11.701246+00:00
-- url     : https://prove2.me/submissions/a69475db-ec26-4335-87dc-e24f15cb29b9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMult_bordered_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.HeckeMult.bordered_cc

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution (i : Fin n) :
    bordered M c r d i.castSucc (Fin.last n) = c i := by simp [bordered]
end GlobalTheory.CompanionTheory.HeckeMult
