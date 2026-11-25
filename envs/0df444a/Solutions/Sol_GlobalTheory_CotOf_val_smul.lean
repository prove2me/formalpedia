-- Prove2me | solution 1 for GlobalTheory.CotOf.val_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:52.091528+00:00
-- url     : https://prove2.me/submissions/b38276e0-1084-4e7b-8586-4cdf65874d35

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open GlobalTheory.CotOf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
variable (D : Dat p g B Tw Dt Oe σ cp)
namespace GlobalTheory.CotOf
theorem _root_.solution {G : Type} [AddCommGroup G] (x : G) (hx : p • x = 0) (n : ℕ) :
    (n : ZMod p).val • x = n • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div n p, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]
end GlobalTheory.CotOf
