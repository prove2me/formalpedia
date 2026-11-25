-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isCyc_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:59.103811+00:00
-- url     : https://prove2.me/submissions/a7f20456-bdfb-4dc2-a91d-91c99dc3e343

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
theorem _root_.solution {T : Tower p Ω} {k : ℕ} {χ χ' : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (h' : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ' g).val) : χ = χ' := by
  funext g
  have e := (h g).symm.trans (h' g)
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff] at e
  simpa using e
end GlobalTheory.K5.Basic
