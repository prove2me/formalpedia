-- Prove2me | solution 1 for GlobalTheory.EisPerB.eisTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:29:03.057153+00:00
-- url     : https://prove2.me/submissions/f8c5cf97-399e-4f1f-8a64-ca5ddacd74f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisensteinStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_card_realEmb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.EisPerB
theorem _root_.solution [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by
  have hprod : ∏ τ, latPt z (a, b) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ (Module.finrank ℚ F) *
      ∏ τ : F →+* ℝ, (((τ b : ℝ) : ℂ) * z τ + ((τ a : ℝ) : ℂ)) := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [latPt]; ring
  unfold eisTerm lhsTerm
  rw [hprod]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_neg, zpow_natCast]
  ring
end GlobalTheory.EisPerB
