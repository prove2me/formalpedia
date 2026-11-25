-- Prove2me | solution 1 for GlobalTheory.SA.TransvG.gram_det_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:19.563551+00:00
-- url     : https://prove2.me/submissions/7cff8cfa-1435-4ccd-9969-7b4d8306c5f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
import Theorems.Thm_GlobalTheory_SA_TransvG_det_gram

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
theorem _root_.solution : LemmaG := fun _ _ _ _ _ _ _ _ F F' => det_gram F F'
end GlobalTheory.SA.TransvG
