-- Prove2me | solution 1 for GlobalTheory.T.isCompact_isOpen_comap_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:11.458521+00:00
-- url     : https://prove2.me/submissions/7244f816-3ab7-4151-a015-9263e091255c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComapMulVecCompactOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Dblock_ComapLat_comap_mulVec_compact_open


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | exact GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | (intros; apply GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open <;> assumption)
end _root_.GlobalTheory.T
