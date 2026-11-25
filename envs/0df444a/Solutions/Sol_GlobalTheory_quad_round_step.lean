-- Prove2me | solution 1 for GlobalTheory.quad_round_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:05:22.016374+00:00
-- url     : https://prove2.me/submissions/58f977b3-1a79-45d7-aed9-573c8c14d8a2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
import Theorems.Thm_GlobalTheory_quad_add_zsmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory
section CosetMin
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
private lemma exists_int_shift_within_bounds (q B N a : ℤ) (hq : 0 < q) (hN : 0 < N) :
    ∃ m : ℤ, -(N * q) ≤ 2 * q * (a + N * m) + B ∧ 2 * q * (a + N * m) + B ≤ N * q := by
  have hD : 0 < 2 * q * N := by positivity
  have h1 := Int.mul_ediv_add_emod (2 * q * a + B + N * q) (2 * q * N)
  have h2 := Int.emod_nonneg (2 * q * a + B + N * q) hD.ne'
  have h3 := Int.emod_lt_of_pos (2 * q * a + B + N * q) hD
  refine ⟨-((2 * q * a + B + N * q) / (2 * q * N)), ?_, ?_⟩
  · linarith
  · linarith
end CosetMin
end GlobalTheory
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
namespace GlobalTheory
theorem _root_.solution (hs : ∀ x y, Bf x y = Bf y x) (hQ : ∀ x, 2 * Q x = Bf x x)
    (y w : X) (hw : 0 ≤ Q w) (N : ℤ) (hN : 0 < N) (a : ℤ) :
    ∃ m : ℤ, 4 * Q (y + (a + N * m) • w) ≤ 4 * Q y + N ^ 2 * Q w := by
  have key : ∀ t : ℤ, Q (y + t • w) = Q y + t * Bf y w + t ^ 2 * Q w :=
    fun t => quad_add_zsmul hs hQ y w t
  rcases hw.lt_or_eq with hq | hq
  · obtain ⟨m, hm1, hm2⟩ := exists_int_shift_within_bounds (Q w) (Bf y w) N a hq hN
    refine ⟨m, ?_⟩
    rw [key]
    set t := a + N * m
    have hsq : (2 * Q w * t + Bf y w) ^ 2 ≤ (N * Q w) ^ 2 := by
      nlinarith
    have hmul : Q w * (4 * (t * Bf y w + t ^ 2 * Q w)) ≤ Q w * (N ^ 2 * Q w) := by
      nlinarith [sq_nonneg (Bf y w)]
    have := le_of_mul_le_mul_left hmul hq
    linarith
  · by_cases hB : 0 ≤ Bf y w
    · refine ⟨-|a|, ?_⟩
      rw [key, ← hq]
      have h1 : a + N * -|a| ≤ 0 := by
        nlinarith [le_abs_self a, abs_nonneg a]
      nlinarith
    · refine ⟨|a|, ?_⟩
      rw [key, ← hq]
      have h1 : 0 ≤ a + N * |a| := by
        nlinarith [neg_abs_le a, abs_nonneg a]
      nlinarith
end GlobalTheory
