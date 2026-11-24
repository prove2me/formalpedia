-- Prove2me | solution 1 for GlobalTheory.MvPoly.finrank_restrictTotalDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:22:52.551794+00:00
-- url     : https://prove2.me/submissions/9e2bba60-b182-43b9-b0d7-ae5c701a7517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_ncard_setOf_degree_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]
namespace GlobalTheory.MvPoly
theorem _root_.solution (R : Type*) [CommRing R] [Nontrivial R] (d : ℕ) :
    Module.finrank R (restrictTotalDegree σ R d) = (Fintype.card σ + d).choose d := by
  rw [← ncard_setOf_degree_le, ← Nat.card_coe_set_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport R _)
end GlobalTheory.MvPoly
