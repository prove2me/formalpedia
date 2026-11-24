-- Prove2me | solution 1 for GlobalTheory.EigenSplit.card_eq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:25:00.631595+00:00
-- url     : https://prove2.me/submissions/70ffccb5-b970-48f0-ab85-fc6fbd54c04e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
omit [DecidableEq ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution (b : Module.Basis ι ℤ (𝓞 E)) :
    Fintype.card ι = Module.finrank ℚ E := by
  rw [← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_basis b]
end GlobalTheory.EigenSplit
