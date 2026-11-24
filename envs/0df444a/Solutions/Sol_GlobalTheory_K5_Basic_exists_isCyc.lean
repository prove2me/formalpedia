-- Prove2me | solution 1 for GlobalTheory.K5.Basic.exists_isCyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:52.019573+00:00
-- url     : https://prove2.me/submissions/dc466c93-765d-4e4c-b203-778dd4bdd1a7

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
theorem _root_.solution (T : Tower p Ω) (k : ℕ) :
    ∃ χ : Gal p Ω → ZMod (p ^ k), ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : ∀ g : Gal p Ω, ∃ a : ZMod (p ^ k), g (T.ζ k) = T.ζ k ^ a.val := by
    intro g
    have : (g (T.ζ k)) ^ (p ^ k) = 1 := by rw [← map_pow, (T.prim k).pow_eq_one, map_one]
    obtain ⟨i, hi, he⟩ := (T.prim k).eq_pow_of_pow_eq_one this
    exact ⟨i, by rw [ZMod.val_cast_of_lt hi, he]⟩
  choose a ha using this
  exact ⟨a, ha⟩
end GlobalTheory.K5.Basic
