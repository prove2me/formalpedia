-- Prove2me | solution 1 for GlobalTheory.UnitCase.jetAt0_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:13.316709+00:00
-- url     : https://prove2.me/submissions/ef14717d-f426-493f-b8a2-35be2af344e3

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
theorem _root_.solution (P : MvPolynomial σ C) (G : MvPowerSeries σ C) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  simp
end GlobalTheory.UnitCase
