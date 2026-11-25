-- Prove2me | solution 1 for GlobalTheory.PDivGroup.eq_zero_of_cobOne_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:42.341823+00:00
-- url     : https://prove2.me/submissions/843e638e-c3ac-491e-be5a-cec4ac1484f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
import Theorems.Thm_GlobalTheory_PDiv_mulBy_of_cobOne_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution [IsDomain O] (hp : (p : O) ≠ 0) (n : ℕ) {b : G.A n}
    (hb : cobOne O _ b = 0) : b = 0 := by
  obtain ⟨h1, h2⟩ := mulBy_of_cobOne_eq_zero hb (p ^ n)
  rw [G.mulBy_pow_self, h2, map_zero, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hp)
end GlobalTheory.PDivGroup
