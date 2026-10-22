-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_transcendental_finiteDimensional_adjoin_of_trdeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:58:22.676531+00:00
-- url     : https://prove2.me/submissions/ce008c88-9879-4b65-9773-f53bc8b717fa

import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Tactic

open IntermediateField

set_option maxHeartbeats 800000

/-- From essential finite type and transcendence degree one, a single transcendental
generator yields a finite extension of the simple transcendental adjunction. -/
theorem solution
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] (htrdeg : Algebra.trdeg K E = 1) :
    ∃ t : E, Transcendental K t ∧
      Module.Finite (IntermediateField.adjoin K ({t} : Set E)) E := by
  have : FinTrdeg K E := inferInstance
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis (K := K) (L := E)
  have hcard : s.card = 1 := by
    have hmk := hs.cardinalMk_eq_trdeg
    have h1 : Cardinal.mk ↥s = 1 := by simpa [htrdeg] using hmk
    have : (s.card : Cardinal) = 1 := by
      calc (s.card : Cardinal)
          _ = (Fintype.card ↥s : Cardinal) := by rw [Fintype.card_coe]
          _ = (Nat.card ↥s : Cardinal) := by rw [Nat.card_eq_fintype_card]
          _ = Cardinal.mk ↥s := Nat.cast_card
          _ = 1 := h1
    exact_mod_cast this
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, ?trans, ?fin⟩
  case trans =>
    exact hs.1.transcendental ⟨t, by simp⟩
  case fin =>
    have hrange : Set.range ((↑) : ({t} : Finset E) → E) = ({t} : Set E) := by
      ext x; simp
    have halg : Algebra.IsAlgebraic (adjoin K (Set.range ((↑) : ({t} : Finset E) → E))) E :=
      hs.isAlgebraic_field
    rw [hrange] at halg
    have : Algebra.EssFiniteType (adjoin K ({t} : Set E)) E :=
      Algebra.EssFiniteType.of_comp (R := K) (S := adjoin K ({t} : Set E)) (T := E)
    exact Algebra.finite_of_essFiniteType_of_isAlgebraic
