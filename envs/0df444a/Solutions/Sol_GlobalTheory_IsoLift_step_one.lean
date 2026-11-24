-- Prove2me | solution 1 for GlobalTheory.IsoLift.step_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:08:37.09196+00:00
-- url     : https://prove2.me/submissions/78b8afc2-80f3-4c40-a67e-e61b0cd106d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
import Theorems.Thm_GlobalTheory_IsoLift_step_coprime_one
import Theorems.Thm_GlobalTheory_SimLift_IsSimMod_of_dvd
import Theorems.Thm_GlobalTheory_SimLift_modN_of_dvd_modulus
import Theorems.Thm_GlobalTheory_SimLift_modN_trans
import Theorems.Thm_GlobalTheory_SimLift_step_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.IsoLift
theorem _root_.solution (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La), IsSimMod D n f 1 →
    ∃ f', IsSimMod D (n * m) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f hf
    exact ⟨f, by simpa using hf, fun a => ⟨0, by simp⟩⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f', IsSimMod D (n * p) f' 1 ∧ (∀ a, D.ModN n (f' a - f a)) := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2⟩
      · exact step_coprime_one D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, h1, h2⟩ := h1
    obtain ⟨f₂, h4, h5⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ h1
    exact ⟨f₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x)⟩
end GlobalTheory.IsoLift
