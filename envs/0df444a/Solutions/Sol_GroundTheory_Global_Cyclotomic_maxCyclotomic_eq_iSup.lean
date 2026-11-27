-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.maxCyclotomic_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:25.77153+00:00
-- url     : https://prove2.me/submissions/8892fa97-be27-4f15-afcb-8c3af0ed0228

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : maxCyclotomic = ⨆ n : ℕ+, rootsOfUnityField n := by
  refine le_antisymm (adjoin_le_iff.mpr ?_) (iSup_le fun n => adjoin_le_iff.mpr ?_)
  · rintro x ⟨n, hn, hx⟩
    exact le_iSup (fun n : ℕ+ => rootsOfUnityField n) ⟨n, hn⟩ (subset_adjoin ℚ _ hx)
  · intro x hx
    exact subset_adjoin ℚ _ ⟨n, n.pos, hx⟩
end GroundTheory.Global.Cyclotomic
