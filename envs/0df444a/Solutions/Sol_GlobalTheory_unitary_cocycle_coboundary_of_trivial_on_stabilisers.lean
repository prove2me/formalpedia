-- Prove2me | solution 1 for GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:30.131954+00:00
-- url     : https://prove2.me/submissions/e618d7ab-ebed-46b7-aef7-5d80a7ff9625

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCocycleCoboundaryOfTrivialOnStabilisers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {X G : Type} [Group G] (mv : X → G → X) (z : X → G → ℂ), (∀ x, mv x 1 = x) →
      (∀ x g g', mv x (g * g') = mv (mv x g) g') → (∀ x g, ‖z x g‖ = 1) →
      (∀ x g g', z x (g * g') = z x g * z (mv x g) g') → (∀ x g, mv x g = x → z x g = 1) →
      ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ x g, c x * z x g = c (mv x g) := by
  intro X G _ mv z h1 hmul hn hz hs
  have key : ∀ b h h', mv b h = mv b h' → z b h = z b h' := by
    intro b h h' e
    have e1 : mv b (h * h'⁻¹) = b := by
      rw [hmul, e, ← hmul, mul_inv_cancel, h1]
    have e2 := hz b (h * h'⁻¹) h'
    rw [hs b _ e1, e1, one_mul, inv_mul_cancel_right] at e2
    exact e2
  let s : Setoid X :=
    { r := fun x y => ∃ g, mv x g = y
      iseqv :=
        { refl := fun x => ⟨1, h1 x⟩
          symm := by
            rintro x y ⟨g, rfl⟩
            exact ⟨g⁻¹, by rw [← hmul, mul_inv_cancel, h1]⟩
          trans := by
            rintro x y w ⟨g, rfl⟩ ⟨g', rfl⟩
            exact ⟨g * g', hmul _ _ _⟩ } }
  let b : X → X := fun x => (Quotient.mk s x).out
  have hb : ∀ x, ∃ g, mv (b x) g = x := fun x => Quotient.mk_out (s := s) x
  have hbe : ∀ x g, b (mv x g) = b x := by
    intro x g
    have : Quotient.mk s (mv x g) = Quotient.mk s x :=
      (Quotient.sound (s := s) (⟨g, rfl⟩ : ∃ g', mv x g' = mv x g)).symm
    simp only [b, this]
  choose γ hγ using hb
  refine ⟨fun x => z (b x) (γ x), fun x => hn _ _, fun x g => ?_⟩
  have e := hz (b x) (γ x) g
  rw [hγ] at e
  have e' := hγ (mv x g)
  show z (b x) (γ x) * z x g = z (b (mv x g)) (γ (mv x g))
  rw [hbe] at e' ⊢
  rw [← e]
  apply key
  rw [hmul, hγ, e']
end GlobalTheory
