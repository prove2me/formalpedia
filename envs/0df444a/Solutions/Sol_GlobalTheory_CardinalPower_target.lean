-- Prove2me | solution 1 for GlobalTheory.CardinalPower.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:25.993081+00:00
-- url     : https://prove2.me/submissions/eafc56cd-ce14-423d-9e18-3b6cd64c5c92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowCardEq
import Theorems.Thm_GlobalTheory_CardinalPower_exists_pow_card_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardinalPower
open IntermediateField
namespace GlobalTheory.CardinalPower
theorem _root_.solution : ∀ {K L : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : Field L]
    [inst_3 : Algebra K L] [Algebra.IsAlgebraic K L] (σ : Gal(L/K)) (X : Finset L),
    ∃ (i : ℕ), ∀ x ∈ X, (σ : L → L) x = x ^ Fintype.card K ^ i :=
  fun σ X => exists_pow_card_eq σ X
end GlobalTheory.CardinalPower
