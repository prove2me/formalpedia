-- Prove2me | solution 1 for GlobalTheory.SA.TransvG.det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:03:58.653816+00:00
-- url     : https://prove2.me/submissions/0b4524ab-cd10-4fbe-8c0e-c8d2115f6a55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
import Theorems.Thm_GlobalTheory_SA_TransvG_det_fromBlocks_last
import Theorems.Thm_GlobalTheory_SA_TransvG_gram_eq_fromBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix
open GlobalTheory GlobalTheory.SA GlobalTheory.SA.TransvG
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.SA.TransvG
theorem _root_.solution (F F' : FlagD H r) : (Gram F F').det = (-1) ^ (r + 1) * Gval F F' := by
  rw [gram_eq_fromBlocks, det_fromBlocks_last, ← conjTranspose_submatrix, det_conjTranspose, det_conjTranspose]
  rfl
end GlobalTheory.SA.TransvG
