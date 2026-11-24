-- Prove2me | solution 1 for GlobalTheory.doubleCoset_semidirect_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:04.888138+00:00
-- url     : https://prove2.me/submissions/29a5db53-5126-4633-b8c2-065590cc5118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSemidirectRepSurjective

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
    ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P),
      (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) →
      ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N),
        (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) →
        ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM →
          (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) →
          (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) →
          ∀ d : DoubleCoset.Quotient (TP : Set P) (KP : Set P), ∃ X : N,
            DoubleCoset.mk TP KP (s (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) * u X)
              = d := by
  intro P M N _ _ _ s π u hs _ hker KP KM L hKs _ _ TM CM TP CP _ hTP _ _ d
  obtain ⟨t, ht, k, hk, hm⟩ := (DoubleCoset.eq TM KM
    (Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d)))) (π (Quotient.out d))).1
    (DoubleCoset.out_eq' TM KM _)
  generalize Quotient.out (DoubleCoset.mk TM KM (π (Quotient.out d))) = q at hm ⊢
  obtain ⟨X, hX⟩ := (hker ((s q)⁻¹ * (s t)⁻¹ * Quotient.out d * (s k)⁻¹)).1 (by
    simp only [map_mul, map_inv, hs]
    rw [hm]; group)
  refine ⟨X, ?_⟩
  rw [hX]
  conv_rhs => rw [← DoubleCoset.out_eq' TP KP d]
  rw [DoubleCoset.eq]
  exact ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, s k, hKs k hk, by group⟩
end GlobalTheory
