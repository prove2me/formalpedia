-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isKum_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:44.181243+00:00
-- url     : https://prove2.me/submissions/8a40e273-1183-4e5a-a2ce-bbb4d041210b

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
theorem _root_.solution {T : Tower p Ω} {n : ℕ} {χ : Gal p Ω → ZMod (p ^ n)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val)
    {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H r a) {g h : Gal p Ω} (hg : g ∈ H) (hh : h ∈ H) :
    a (g * h) = a g + χ g * a h := by
  have e := ha (g * h) (H.mul_mem hg hh)
  rw [AlgEquiv.mul_apply, ha h hh, map_mul, map_pow, hχ g, ha g hg, ← pow_mul, ← mul_assoc,
    ← pow_add] at e
  have e' := mul_right_cancel₀ hr e
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e'
  simpa [add_comm] using e'.symm
end GlobalTheory.K5.Basic
