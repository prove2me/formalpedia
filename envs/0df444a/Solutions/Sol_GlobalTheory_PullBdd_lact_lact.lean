-- Prove2me | solution 1 for GlobalTheory.PullBdd.lact_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:10.048802+00:00
-- url     : https://prove2.me/submissions/c7fa1b89-9089-4613-80d4-65fc2a60f453

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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (β γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact β (lact γ x) = lact (β * γ) x := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
      Matrix (Fin r) (Fin r) ℂ) =
    ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
end GlobalTheory.PullBdd
