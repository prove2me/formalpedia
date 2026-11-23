-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMult.one_cl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:13.791793+00:00
-- url     : https://prove2.me/submissions/afaa8706-b386-4017-9fa6-7c4b1efad442

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
namespace GlobalTheory.CompanionTheory.HeckeMult
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc (Fin.last n) = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne
end GlobalTheory.CompanionTheory.HeckeMult
