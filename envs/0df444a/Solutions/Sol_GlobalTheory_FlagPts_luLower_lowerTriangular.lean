-- Prove2me | solution 1 for GlobalTheory.FlagPts.luLower_lowerTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:17.038671+00:00
-- url     : https://prove2.me/submissions/929b1eaa-2561-4e35-95ed-3618c6c60079

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LuLowerLowerTriangular
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.FlagPts
theorem _root_.solution (P : Matrix (Fin n) (Fin n) k) : (luLower P).BlockTriangular OrderDual.toDual :=
  fun a m h => by
    have h' : a < m := by simpa using h
    simp [luLower, h'.ne, not_lt.2 h'.le]
end GlobalTheory.FlagPts
