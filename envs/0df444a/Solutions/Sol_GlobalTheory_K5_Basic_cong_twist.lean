-- Prove2me | solution 1 for GlobalTheory.K5.Basic.cong_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:01:01.793374+00:00
-- url     : https://prove2.me/submissions/21558cb1-9636-49f9-877f-50ede6618a06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_isInt_gal
import Theorems.Thm_GlobalTheory_K5_Basic_cong_mul_right
import Theorems.Thm_GlobalTheory_K5_Basic_cong_natCast
import Theorems.Thm_GlobalTheory_K5_Basic_isCyc_eq_one_iff

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
theorem _root_.solution {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val) (j : ℕ)
    {g : Gal p Ω} (hg : g (T.ζ k) = T.ζ k) {x : Ω} (hx : IsInt p x) :
    Cong p k (((χ g).val : Ω) ^ j * g x) (g x) := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e : (χ g).val ^ j ≡ 1 [MOD p ^ k] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ZMod.natCast_zmod_val,
      (isCyc_eq_one_iff hχ g).2 hg]
    simp
  have := cong_mul_right (cong_natCast (Ω := Ω) e) (isInt_gal g hx)
  rwa [Nat.cast_pow, Nat.cast_one, one_mul] at this
end GlobalTheory.K5.Basic
