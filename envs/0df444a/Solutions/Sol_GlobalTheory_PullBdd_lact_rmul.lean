-- Prove2me | solution 1 for GlobalTheory.PullBdd.lact_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:06.014493+00:00
-- url     : https://prove2.me/submissions/ae23889f-d1af-471b-9ad3-275873df0192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PullBdd
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (β : GL (Fin r) E) (x b : Frame Ψ r) :
    lact β (rmul x b) = rmul (lact β x) b := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]
end GlobalTheory.PullBdd
