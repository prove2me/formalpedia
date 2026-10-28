-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_componentLocalLength_bound_of_height
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-25T07:26:08.71411+00:00
-- url     : https://prove2.me/submissions/35c50610-7ea8-4382-a698-598159592540

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution :
    ¬ (∀ {m : Nat} (w : Fin (m + 1) → Rat)
        (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
        (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
        (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
        (hminimal :
          (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
        (hdegree : ∀ f ∈ S, logarithmicDegreeBound w H f)
        (A : Finset (Fin (m + 1)))
        (hcodim : (A.card : ℕ∞) = P.height)
        (L : Nat)
        (hlength :
          componentLocalLength
            (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
              (L : ENat)),
        (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card) := by
  intro h
  let w : Fin 2 → Rat := fun i => if i = 0 then 3 else 1
  let x : MvPolynomial (Fin 2) Complex := MvPolynomial.X 1
  let P : Ideal (MvPolynomial (Fin 2) Complex) := Ideal.span {x}
  let S : Finset (MvPolynomial (Fin 2) Complex) := {x}
  let A : Finset (Fin 2) := {0}
  have hx0 : x ≠ 0 := by
    dsimp [x]
    exact MvPolynomial.X_ne_zero 1
  have hxprime : Prime x := by
    dsimp [x]
    exact MvPolynomial.X_prime
  haveI : P.IsPrime := by
    dsimp [P]
    exact (Ideal.span_singleton_prime hx0).2 hxprime
  let I : Ideal (MvPolynomial (Fin 2) Complex) := Ideal.span (↑S : Set _)
  have hI : I = P := by
    simp [I, P, S]
  have hminP : P.IsMinimalPrime P := by
    refine ⟨⟨inferInstance, le_rfl⟩, ?_⟩
    intro Q hQ hQP
    exact hQ.2
  have hminimal : I.IsMinimalPrime P := by
    rw [hI]
    exact hminP
  have hheight_le : P.height ≤ 1 := by
    apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
    simpa [Ideal.minimalPrimes] using hminP
  have hheight_ge : 1 ≤ P.height := by
    dsimp [P]
    apply Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    exact mem_nonZeroDivisors_iff_ne_zero.mpr hx0
  have hheight : P.height = 1 := le_antisymm hheight_le hheight_ge
  have hcodim : (A.card : ℕ∞) = P.height := by
    simp [A, hheight]
  have hw : ∀ i, 0 < (w i : Real) := by
    intro i
    fin_cases i <;> norm_num [w]
  have hH : (0 : Real) < 1 := by norm_num
  have hdegree : ∀ f ∈ S, logarithmicDegreeBound w 1 f := by
    intro f hf
    have hf' : f = x := Finset.mem_singleton.mp hf
    subst f
    rw [logarithmicDegreeBound, MvPolynomial.support_X]
    intro a ha
    simp only [Finset.mem_singleton] at ha
    subst a
    simp [w]
  have hlength : componentLocalLength I P = (1 : ENat) := by
    rw [hI]
    change Module.length (Localization.AtPrime P)
      ((Localization.AtPrime P) ⧸
        P.map (algebraMap _ (Localization.AtPrime P))) = (1 : ENat)
    rw [Module.length_eq_one_iff]
    apply isSimpleModule_iff_isCoatom.mpr
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).1
  have hbad := h (m := 1) w hw 1 hH S P hminimal hdegree A hcodim 1 hlength
  norm_num [A, w] at hbad