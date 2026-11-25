-- Prove2me | solution 1 for GlobalTheory.DetPowPairing.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:24.486238+00:00
-- url     : https://prove2.me/submissions/a4ecbc6c-2379-47ac-8d51-90683052746e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_eq
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution :
    (∀ (C : Type) [Field C] [CharZero C] (n₀ x : ℕ), (∏ c ∈ Finset.range n₀, (c.factorial : C)) * (∑ A ∈ (cayDet n₀ C ^ x).support, MvPolynomial.coeff A (cayDet n₀ C ^ x) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ x)) = ∏ c ∈ Finset.range n₀, ((x + c).factorial : C)) := by
  intro C _ _ n₀ x
  have h := pair_pow (C := C) n₀ x
  rw [pair_eq] at h
  exact h
end GlobalTheory.DetPowPairing
