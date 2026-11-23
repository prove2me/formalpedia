-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.bordered_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:00.086899+00:00
-- url     : https://prove2.me/submissions/682694c6-78c9-4e6e-b650-5f939094cb74

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution (i j : Fin n) :
    bordered M c r d i.castSucc j.castSucc = M i j := by simp [bordered]
end GlobalTheory.CompanionTheory.HeckeMult
