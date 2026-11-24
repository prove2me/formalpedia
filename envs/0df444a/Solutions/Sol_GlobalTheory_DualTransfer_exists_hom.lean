-- Prove2me | solution 1 for GlobalTheory.DualTransfer.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:05.487303+00:00
-- url     : https://prove2.me/submissions/a11432a6-e9fc-40cf-aaa1-fb29a8feb2d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer
namespace GlobalTheory.DualTransfer
theorem _root_.solution {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (h1 : ∀ a a' b, e (a + a') b = e a b * e a' b) (h2 : ∀ a b b', e a (b + b') = e a b * e a b')
    (h3 : ∀ b, e 0 b = 1) (h4 : ∀ a, e a 0 = 1) (M : AddSubgroup A)
    (hM : ∀ a ∈ M, ∀ b, e a b = 1) :
    ∃ f : B →+ AddChar (A ⧸ M) ℂ, ∀ b (a : A), f b (a : A ⧸ M) = e a b := by
  have key : ∀ b (a a' : A), -a + a' ∈ M → e a b = e a' b := by
    intro b a a' h
    have ha : a' = a + (-a + a') := by abel
    rw [ha, h1, hM _ h b, mul_one]
  let ψ : B → AddChar (A ⧸ M) ℂ := fun b =>
    { toFun := fun q => Quotient.liftOn' q (fun a => e a b)
        (fun a a' h => key b a a' (QuotientAddGroup.leftRel_apply.mp h))
      map_zero_eq_one' := h3 b
      map_add_eq_mul' := by
        intro q q'
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
        obtain ⟨a', rfl⟩ := QuotientAddGroup.mk_surjective q'
        exact h1 a a' b }
  refine ⟨{ toFun := ψ, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h4 a
  · intro b b'
    ext q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h2 a b b'
  · intro b a
    rfl
end GlobalTheory.DualTransfer
