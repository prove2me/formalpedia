-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isKum_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:55:14.971834+00:00
-- url     : https://prove2.me/submissions/e5506583-6c82-4a67-b2b5-d2a131a65aa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_cong_natCast
import Theorems.Thm_GlobalTheory_K5_Basic_isKum_mul

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
theorem _root_.solution {T : Tower p Ω} {n : ℕ} {χ : Gal p Ω → ZMod (p ^ n)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val)
    {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H r a) {g h : Gal p Ω} (hg : g ∈ H) (hh : h ∈ H) :
    Cong p n (((χ g).val : Ω) ^ 1 * g ((a h).val : Ω) - ((a (g * h)).val : Ω) + ((a g).val : Ω)) 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e : (χ g).val * (a h).val + (a g).val ≡ (a (g * h)).val [MOD p ^ n] := by
    rw [← ZMod.natCast_eq_natCast_iff, isKum_mul hχ hr ha hg hh]
    simp [add_comm]
  obtain ⟨z, hz, ez⟩ := cong_natCast (Ω := Ω) e
  refine ⟨z, hz, ?_⟩
  rw [map_natCast, ← ez]
  push_cast
  ring
end GlobalTheory.K5.Basic
