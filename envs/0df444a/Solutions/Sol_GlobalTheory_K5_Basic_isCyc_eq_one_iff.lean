-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isCyc_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:14.139834+00:00
-- url     : https://prove2.me/submissions/51902759-6d92-4832-978a-b92f8ae75412

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
theorem _root_.solution {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g : Gal p Ω) : χ g = 1 ↔ g (T.ζ k) = T.ζ k := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [h g]
  conv_rhs => rhs; rw [← pow_one (T.ζ k)]
  rw [zeta_pow_eq_iff, ← ZMod.natCast_eq_natCast_iff]
  simp
end GlobalTheory.K5.Basic
