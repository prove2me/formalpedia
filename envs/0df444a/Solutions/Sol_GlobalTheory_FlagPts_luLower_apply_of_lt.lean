-- Prove2me | solution 1 for GlobalTheory.FlagPts.luLower_apply_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:16.155531+00:00
-- url     : https://prove2.me/submissions/48755956-b6fa-4be6-b10b-c63e20651d9e

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
theorem _root_.solution (P : Matrix (Fin n) (Fin n) k) {a m : Fin n} (h : m < a) :
    luLower P a m = luNum P a m / leadMinor P m := by
  simp [luLower, h, h.ne']
end GlobalTheory.FlagPts
