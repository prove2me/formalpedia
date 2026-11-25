-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.not_allMatch_rank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:42:06.014343+00:00
-- url     : https://prove2.me/submissions/9ea2e8e8-6a45-4883-b500-612e12110c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_GlobalTheory_Ex_tate_int
import Theorems.Thm_GlobalTheory_Ex_tate_tors


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
theorem _root_.solution : ¬ AllMatch fun {_} _ {N} {_} {_} _ _ _ => Subsingleton N.X := by
  intro h
  have h2 : ((2 : ℕ) : ℂ_[2]) ≠ 0 := Nat.cast_ne_zero.2 two_ne_zero
  have n2 : ‖((2 : ℕ) : ℂ_[2])‖ < 1 := by
    have : ‖((2 : ℕ) : ℂ_[2])‖ = ‖((2 : ℕ) : ℚ_[2])‖ := by
      rw [← map_natCast (algebraMap ℚ_[2] ℂ_[2]), norm_algebraMap']
    rw [this]; exact Padic.norm_p_lt_one
  have n3 : ‖((3 : ℕ) : ℂ_[2])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[2] ℂ_[2]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 (by norm_num)
  have := h ℂ_[2] (tate (Units.mk0 _ h2)) (tate (Units.mk0 _ h2)) _ _ 3 0 0 Nat.prime_three (by decide) n3
    (tate_int _ n2) (tate_int _ n2) (tate_tors _ _) (tate_tors _ _) (tateMatch _ 3 (by decide))
  exact absurd (show (0 : ℤ) = 1 from this.elim (0 : ℤ) (1 : ℤ)) zero_ne_one
end GlobalTheory.Ex.TateInh
