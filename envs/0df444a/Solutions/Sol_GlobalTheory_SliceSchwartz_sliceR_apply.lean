-- Prove2me | solution 1 for GlobalTheory.SliceSchwartz.sliceR_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:22.44481+00:00
-- url     : https://prove2.me/submissions/f6516792-5c77-4aa0-81d0-68a63b188174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SliceSchwartz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceSchwartz
theorem _root_.solution {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := rfl
end GlobalTheory.SliceSchwartz
