-- Prove2me | solution 1 for GlobalTheory.FlagPts.luLower_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:58.90152+00:00
-- url     : https://prove2.me/submissions/06a53171-38b5-47f5-8e2b-924fc7817d9a

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
theorem _root_.solution (P : Matrix (Fin n) (Fin n) k) (a : Fin n) : luLower P a a = 1 := by
  simp [luLower]
end GlobalTheory.FlagPts
