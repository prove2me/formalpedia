-- Prove2me | solution 1 for GlobalTheory.UnitCase.jetAt0_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:12.122091+00:00
-- url     : https://prove2.me/submissions/3a0f96ae-add1-45b8-b303-f30c9678c919

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_jetAt0_eq_sum

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
theorem _root_.solution (m : σ →₀ ℕ) (c : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.monomial m c) G = c * (mfact m : C) * MvPowerSeries.coeff m G := by
  classical
  rw [jetAt0_eq_sum _ G {m} MvPolynomial.support_monomial_subset]
  simp
end GlobalTheory.UnitCase
