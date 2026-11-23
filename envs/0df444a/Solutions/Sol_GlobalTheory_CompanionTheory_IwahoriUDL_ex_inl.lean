-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.ex_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:00.935017+00:00
-- url     : https://prove2.me/submissions/87d893ff-72fb-4970-8244-70352c852968

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
theorem _root_.solution {n : ℕ} (i : Fin n) : ex n (Sum.inl i) = i.castSucc := rfl
end GlobalTheory.CompanionTheory.IwahoriUDL
