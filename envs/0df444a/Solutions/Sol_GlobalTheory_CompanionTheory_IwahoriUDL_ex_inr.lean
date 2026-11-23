-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.ex_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:00.866535+00:00
-- url     : https://prove2.me/submissions/503aaf6f-f814-406a-a361-9219e4040c9d

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
theorem _root_.solution {n : ℕ} (k : Fin 1) : ex n (Sum.inr k) = Fin.last n := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  ext
  simp [ex]
end GlobalTheory.CompanionTheory.IwahoriUDL
