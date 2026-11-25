-- Prove2me | solution 1 for GroundTheory.LocalField.powerSeries_ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:22.769358+00:00
-- url     : https://prove2.me/submissions/c37653b7-d002-40e6-a1de-d944f16f58cd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B S : Type*} [CommRing B] [CommRing S]
namespace GroundTheory.LocalField
theorem _root_.solution {J : Ideal S} (hJ : ∀ z : S, (∀ k : ℕ, z ∈ J ^ k) → z = 0)
    {Φ₁ Φ₂ : B⟦X⟧ →+* S} (hC : ∀ b : B, Φ₁ (C b) = Φ₂ (C b)) (hX : Φ₁ X = Φ₂ X)
    (hXJ : Φ₁ X ∈ J) : Φ₁ = Φ₂ := by
  have hpoly : Φ₁.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) =
      Φ₂.comp (Polynomial.coeToPowerSeries.ringHom (R := B)) := by
    apply Polynomial.ringHom_ext
    · intro b
      simpa using hC b
    · simpa using hX
  have hp : ∀ p : Polynomial B, Φ₁ (p : B⟦X⟧) = Φ₂ (p : B⟦X⟧) := fun p =>
    congrArg (fun Φ : Polynomial B →+* S => Φ p) hpoly
  ext F
  refine sub_eq_zero.mp (hJ _ fun k => ?_)
  set G : B⟦X⟧ := PowerSeries.mk fun i => coeff (i + k) F
  have hF : Φ₁ F - Φ₂ F = Φ₁ X ^ k * (Φ₁ G - Φ₂ G) := by
    conv_lhs => rw [F.eq_X_pow_mul_shift_add_trunc k]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, hp, ← hX]
    ring
  rw [hF]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXJ k)
end GroundTheory.LocalField
