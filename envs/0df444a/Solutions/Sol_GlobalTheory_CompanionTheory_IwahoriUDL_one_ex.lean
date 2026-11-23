-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.one_ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:36.556818+00:00
-- url     : https://prove2.me/submissions/4fa62428-b616-4ddc-9420-1f2847febf3d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.IwahoriUDL
theorem _root_.solution {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ex n i) (ex n j) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) i j := by
  rw [fromBlocks_one]
  simp [Matrix.one_apply]
end GlobalTheory.CompanionTheory.IwahoriUDL
