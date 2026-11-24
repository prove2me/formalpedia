-- Prove2me | solution 1 for GlobalTheory.SS.Dil.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:16:40.542425+00:00
-- url     : https://prove2.me/submissions/1e216cb7-d320-484f-995c-89c998c4d39a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R B B' S : Type} [CommRing R] [CommRing B] [CommRing B'] [CommRing S] [Algebra R B] [Algebra R B']
    [Algebra R S] (φ : B →ₐ[R] B') (π : R) (I : Ideal B) (hinj : Function.Injective φ)
    (hden : ∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b)
    (hgen : ∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x)
    (a : B →ₐ[R] S) (hreg : algebraMap R S π ∈ nonZeroDivisors S) (ha : ∀ g ∈ I, algebraMap R S π ∣ a g) :
    ∃ a' : B' →ₐ[R] S, a'.comp φ = a := by
  let Rel : B' → S → Prop := fun b' s => ∃ (k : ℕ) (b : B), algebraMap R B' π ^ k * b' = φ b ∧
    algebraMap R S π ^ k * s = a b
  have radd : ∀ x y s t, Rel x s → Rel y t → Rel (x + y) (s + t) := by
    rintro x y s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    refine ⟨k + l, algebraMap R B π ^ l * b + algebraMap R B π ^ k * c, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, φ.commutes, ← h1, ← h3]; ring
    · simp only [map_add, map_mul, map_pow, a.commutes, ← h2, ← h4]; ring
  have rmul : ∀ x y s t, Rel x s → Rel y t → Rel (x * y) (s * t) := by
    rintro x y s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    refine ⟨k + l, b * c, ?_, ?_⟩
    · simp only [map_mul, ← h1, ← h3]; ring
    · simp only [map_mul, ← h2, ← h4]; ring
  have rφ : ∀ b, Rel (φ b) (a b) := fun b => ⟨0, b, by simp, by simp⟩
  have runiq : ∀ x s t, Rel x s → Rel x t → s = t := by
    rintro x s t ⟨k, b, h1, h2⟩ ⟨l, c, h3, h4⟩
    have e1 : algebraMap R B π ^ l * b = algebraMap R B π ^ k * c := hinj (by
      rw [map_mul, map_mul, map_pow, map_pow, φ.commutes, ← h1, ← h3]; ring)
    have e2 := congrArg a e1
    simp only [map_mul, map_pow, a.commutes, ← h2, ← h4] at e2
    apply (mul_cancel_left_mem_nonZeroDivisors (pow_mem hreg (k + l))).1
    linear_combination e2
  have rex : ∀ x, ∃ s, Rel x s := by
    refine hgen _ (fun b => ⟨_, rφ b⟩) ?_ ?_ ?_
    · intro g hg b' hb'
      obtain ⟨s, hs⟩ := ha g hg
      exact ⟨s, 1, g, by rwa [pow_one], by rw [pow_one, hs]⟩
    · rintro x y ⟨s, hs⟩ ⟨t, ht⟩; exact ⟨_, radd _ _ _ _ hs ht⟩
    · rintro x y ⟨s, hs⟩ ⟨t, ht⟩; exact ⟨_, rmul _ _ _ _ hs ht⟩
  choose f hf using rex
  have fφ : ∀ b, f (φ b) = a b := fun b => runiq _ _ _ (hf _) (rφ b)
  refine ⟨{ toFun := f
            map_one' := by rw [← map_one φ, fφ, map_one]
            map_zero' := by rw [← map_zero φ, fφ, map_zero]
            map_mul' := fun x y => runiq _ _ _ (hf _) (rmul _ _ _ _ (hf x) (hf y))
            map_add' := fun x y => runiq _ _ _ (hf _) (radd _ _ _ _ (hf x) (hf y))
            commutes' := fun r => by
              show f _ = _
              rw [← φ.commutes, fφ, a.commutes] }, AlgHom.ext fφ⟩
end GlobalTheory.SS.Dil
