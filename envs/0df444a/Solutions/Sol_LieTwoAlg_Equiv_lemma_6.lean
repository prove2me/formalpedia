-- Prove2me | solution 1 for LieTwoAlg.Equiv.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:40:08.307563+00:00
-- url     : https://prove2.me/submissions/76a7d34e-f36e-4675-af77-946f5bf187f7

import Definitions.Def_LieTwoAlg_Equiv_TwoVect

set_option autoImplicit false

open LieTwoAlg.Equiv

universe u

/-- Lemma 6, pp. 9–11: the forced linear composition and its category laws. -/
theorem solution {k : Type u} [Field k] (V : TwoVect k) :
    (∀ f g : V.V1, V.t f = V.s g →
      V.s (V.comp f g) = V.s f ∧ V.t (V.comp f g) = V.t g) ∧
    (∀ f g h : V.V1, V.comp (V.comp f g) h = V.comp f (V.comp g h)) ∧
    (∀ f : V.V1, V.comp (V.i (V.s f)) f = f ∧
      V.comp f (V.i (V.t f)) = f) ∧
    (∀ c : V.composable →ₗ[k] V.V1,
      (∀ f : V.V1, c (V.leftUnitPair f) = f) →
      (∀ f : V.V1, c (V.rightUnitPair f) = f) →
      ∀ p : V.composable, c p = V.comp p.1.1 p.1.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g h
    constructor
    · simp [TwoVect.comp, map_sub, map_add, V.s_i, h]
    · simp [TwoVect.comp, map_sub, map_add, V.t_i]
  · intro f g h
    simp only [TwoVect.comp, map_sub, map_add, V.t_i]
    abel
  · intro f
    constructor <;> simp [TwoVect.comp, V.t_i]
  · intro c hl hr p
    have hp : V.t p.1.1 = V.s p.1.2 := p.2
    have decomp : p = V.rightUnitPair p.1.1 + V.leftUnitPair p.1.2 -
        V.leftUnitPair (V.i (V.t p.1.1)) := by
      apply Subtype.ext
      apply Prod.ext
      · change p.1.1 = p.1.1 + V.i (V.s p.1.2) - V.i (V.s (V.i (V.t p.1.1)))
        rw [V.s_i, hp]
        abel
      · change p.1.2 = V.i (V.t p.1.1) + p.1.2 - V.i (V.t p.1.1)
        abel
    conv_lhs => rw [decomp]
    rw [map_sub, map_add, hr, hl, hl]
    rfl


