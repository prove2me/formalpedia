-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.arcTx_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:52:07.480706+00:00
-- url     : https://prove2.me/submissions/7fc535b3-5d2d-423f-a74d-20433ec31588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution :
    PowerSeries.coeff 1 ((tate (1 : ℤˣ)).arcTx (tateBe 1 1 one_ne_zero).be 1 1) = 2 := by
  rw [NumD.arcTx, PowerSeries.coeff_mk]
  have e : ∀ χ : ℤ, (tate (1 : ℤˣ)).txT 1 1 χ = 1 := fun χ => by
    rw [tate_txT]
    have : sv (1 : (tate (1 : ℤˣ)).QT (1 ^ 2)).1.2 χ = 1 := rfl
    rw [this]; simp
  have : (∑ᶠ (χ : ℤ) (_ : χ ∈ ({1, -1} : Finset ℤ)), (1 : ℤ)) = 2 := by
    rw [finsum_mem_finset_eq_sum]; rfl
  refine Eq.trans ?_ this
  refine finsum_congr fun (χ : ℤ) => ?_
  rw [e]
  refine finsum_congr_Prop (propext ?_) fun _ => rfl
  change (2 * (1 : ℕ) : ℤ) * ((0 + 1 • χ) * (0 + 1 • χ)) / (2 * ((1 : ℕ) : ℤ) ^ 2) = ((1 : ℕ) : ℤ) ↔ _
  simp only [Nat.cast_one, mul_one, one_pow, zero_add, one_smul, Finset.mem_insert, Finset.mem_singleton]
  rw [Int.mul_ediv_cancel_left _ two_ne_zero, mul_self_eq_one_iff]
end GlobalTheory.Ex.TateInh
