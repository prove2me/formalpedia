-- Prove2me | solution 1 for GlobalTheory.SignChar.toZMod_eq_of_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:10.528732+00:00
-- url     : https://prove2.me/submissions/62bb138b-c448-4b54-8c6c-ce6a867de32b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.SignChar
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
namespace GlobalTheory.SignChar
theorem _root_.solution (a : ℤ_[p]) (k : ℕ)
    (h : (Tw.q 0).1 (algebraMap ℤ_[p] (Tw.O : Type) a) = k) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : ¬ IsUnit (a - k) := by
    intro hu
    have h2 := (hu.map (algebraMap ℤ_[p] (Tw.O : Type))).map (Tw.q 0).1
    rw [map_sub, map_sub, h, map_natCast, map_natCast, sub_self] at h2
    exact not_isUnit_zero h2
  have h3 : a - k ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod]
    exact h1
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h3
  exact h3
end GlobalTheory.SignChar
