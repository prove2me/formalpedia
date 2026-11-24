-- Prove2me | solution 1 for GlobalTheory.SA.TransvG.gram_eq_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:04:16.945204+00:00
-- url     : https://prove2.me/submissions/db4a13c3-ffd8-4af4-b529-7520b4223d1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
import Theorems.Thm_GlobalTheory_SA_TransvG_B_e_e

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
theorem _root_.solution (F F' : FlagD H r) :
    Gram F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -F.T else 0) (Zhat F F') (Zhat F F')ᴴ
      (diagonal fun a => if a = Fin.last r then -F'.T else 0) := by
  ext (a | a) (b | b)
  · exact B_e_e F a b
  · rfl
  · exact (H.herm _ _).symm
  · exact B_e_e F' a b
end GlobalTheory.SA.TransvG
