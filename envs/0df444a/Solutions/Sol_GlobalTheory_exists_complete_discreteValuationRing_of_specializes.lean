-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:46.88393+00:00
-- url     : https://prove2.me/submissions/25545348-8706-44a7-bc3c-d50ad756c097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_ker_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{u}}
    [IsLocallyNoetherian X] {η x : X} (h : η ⤳ x) (hne : η ≠ x) :
    ∃ (O : CommRingCat.{u}) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (f : Spec O ⟶ X),
      f (⊥ : PrimeSpectrum O) = η ∧ f (closedPoint O) = x := by
  have h1 : η ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact h
  obtain ⟨q, rfl⟩ := h1
  have hq : q.asIdeal ≠ maximalIdeal (X.presheaf.stalk x) := by
    intro e
    apply hne
    have : q = closedPoint (X.presheaf.stalk x) := PrimeSpectrum.ext e
    rw [this, Scheme.fromSpecStalk_closedPoint]
  have hqp : Ideal.IsPrime (α := X.presheaf.stalk x) q.asIdeal := q.isPrime
  obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_ker_eq (S := X.presheaf.stalk x) q.asIdeal hq
  refine ⟨.of O, hO, hO', hO'', Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (X.fromSpecStalk x) ?_)
    exact PrimeSpectrum.ext h1
  · refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
    exact comap_closedPoint φ
end GlobalTheory
