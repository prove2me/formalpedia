-- Prove2me | solution 1 for GlobalTheory.K5.Basic.exists_isKum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:53.562723+00:00
-- url     : https://prove2.me/submissions/44f528a2-e425-4d08-9235-063d104da832

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (T : Tower p Ω) (n : ℕ) (H : Subgroup (Gal p Ω)) {r : Ω} (hr : r ≠ 0)
    (hH : ∀ g ∈ H, g (r ^ p ^ n) = r ^ p ^ n) : ∃ a, IsKum T n H r a := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : ∀ g : Gal p Ω, ∃ a : ZMod (p ^ n), g ∈ H → g r = T.ζ n ^ a.val * r := by
    intro g
    by_cases hg : g ∈ H
    · have : (g r / r) ^ (p ^ n) = 1 := by
        rw [div_pow, ← map_pow, div_eq_one_iff_eq (pow_ne_zero _ hr), hH g hg]
      obtain ⟨i, hi, he⟩ := (T.prim n).eq_pow_of_pow_eq_one this
      exact ⟨i, fun _ => by rw [ZMod.val_cast_of_lt hi, he, div_mul_cancel₀ _ hr]⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose a ha using this
  exact ⟨a, ha⟩
end GlobalTheory.K5.Basic
