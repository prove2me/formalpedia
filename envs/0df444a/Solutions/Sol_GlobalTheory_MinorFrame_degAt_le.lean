-- Prove2me | solution 1 for GlobalTheory.MinorFrame.degAt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:24.485422+00:00
-- url     : https://prove2.me/submissions/3c2df7a6-db08-48d2-91d1-a11f99076e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : degAt τ₀ t ≤ t.sum fun _ e => e := by
  unfold degAt Finsupp.sum
  exact Finset.sum_le_sum fun y _ => by beta_reduce; split_ifs <;> omega
end GlobalTheory.MinorFrame
