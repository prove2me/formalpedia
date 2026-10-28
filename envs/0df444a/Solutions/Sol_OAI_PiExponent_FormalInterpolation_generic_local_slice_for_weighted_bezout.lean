-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.generic_local_slice_for_weighted_bezout
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T21:30:59.922508+00:00
-- url     : https://prove2.me/submissions/5c582f9c-d8aa-4c1b-bc86-639833fa8a89
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_generic_slice
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_component_local_length_mono

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ g ∈ S, logarithmicDegreeBound w H g)
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height)
    (L : Nat)
    (hlength :
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
          (L : ENat)) :
    ∃ f : Fin A.card → MvPolynomial (Fin (m + 1)) Complex,
      (∀ j, f j ∈ Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) ∧
      (∀ j, logarithmicDegreeBound w H (f j)) ∧
      (Ideal.span (Set.range f)).IsMinimalPrime P ∧
      ∃ M : Nat,
        componentLocalLength (Ideal.span (Set.range f)) P = (M : ENat) ∧
        L ≤ M := by
  obtain ⟨f, hfmem, hfdegree, hfmin⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_generic_slice
      w hw H hH S P hminimal hdegree A hcard
  have hJI :
      Ideal.span (Set.range f) ≤
        Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex)) := by
    refine Ideal.span_le.2 ?_
    rintro x ⟨j, rfl⟩
    exact hfmem j
  obtain ⟨M, hM, hLM⟩ :=
    OAI.PiExponent.FormalInterpolation.component_local_length_mono
      (Ideal.span (Set.range f))
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex)))
      P L hlength hJI
  exact ⟨f, hfmem, hfdegree, hfmin, M, hM, hLM⟩