-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_zero_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:52.640042+00:00
-- url     : https://prove2.me/submissions/215d3d5b-497d-43b8-9ec8-67497f828157

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
theorem _root_.solution (a : MvPowerSeries σ C) : MvPowerSeries.coeff 0 (mvExp a) = 1 := by
  change ∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), _ = _
  simp
end GlobalTheory.UnitCase
