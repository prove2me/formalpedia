-- Prove2me | solution 1 for GlobalTheory.HTLat.map_mkQ_step_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:45:34.564949+00:00
-- url     : https://prove2.me/submissions/388b635a-acc6-4daa-81d6-3c058bee51f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_step_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
namespace GlobalTheory.HTLat
theorem _root_.solution (f : Fin N → U) (i : Fin N) :
    (step C f (i + 1)).map (step C f i).mkQ = Submodule.span C {(step C f i).mkQ (f i)} := by
  rw [step_succ, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span,
    Set.image_singleton]
end GlobalTheory.HTLat
