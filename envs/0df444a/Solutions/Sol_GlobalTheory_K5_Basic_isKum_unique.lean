-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isKum_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:18.60414+00:00
-- url     : https://prove2.me/submissions/d9278ed1-94b4-4bec-b83f-1537b7865a59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_zeta_pow_eq_iff

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
theorem _root_.solution {T : Tower p Ω} {n : ℕ} {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0)
    {a b : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H r a) (hb : IsKum T n H r b) {g : Gal p Ω}
    (hg : g ∈ H) : a g = b g := by
  have h := mul_right_cancel₀ hr ((ha g hg).symm.trans (hb g hg))
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at h
  simpa using h
end GlobalTheory.K5.Basic
