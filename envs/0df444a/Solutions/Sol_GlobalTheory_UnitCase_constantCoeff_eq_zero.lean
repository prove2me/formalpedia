-- Prove2me | solution 1 for GlobalTheory.UnitCase.constantCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:01.545668+00:00
-- url     : https://prove2.me/submissions/9bf89c66-2109-40d9-bf92-ad1ffab8a627

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {l n0 : ℕ}
    {h1 : MvPowerSeries (PVar n0) C} (H : MplusRows v l n0 h1) :
    MvPowerSeries.constantCoeff h1 = 0 := by
  by_contra h
  have := H.2.1 0 h
  simp [degR] at this
end GlobalTheory.UnitCase
