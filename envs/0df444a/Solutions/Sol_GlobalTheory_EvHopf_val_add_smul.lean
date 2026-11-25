-- Prove2me | solution 1 for GlobalTheory.EvHopf.val_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:35.453391+00:00
-- url     : https://prove2.me/submissions/6e618307-e848-4206-bb7c-8d46b9382d45

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHopfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvHopfOfTensorLocal

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
set_option linter.style.haveILetI false
open GlobalTheory GlobalTheory.EvHopf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
namespace GlobalTheory.EvHopf
theorem _root_.solution {M : Type} [AddCommGroup M] (x : M) (hx : p • x = 0) (a b : ZMod p) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← add_smul]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p, add_smul, mul_comm, mul_smul, hx,
    smul_zero, add_zero]
end GlobalTheory.EvHopf
