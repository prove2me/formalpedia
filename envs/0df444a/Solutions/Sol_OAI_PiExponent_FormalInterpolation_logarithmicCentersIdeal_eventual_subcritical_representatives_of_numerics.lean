-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCentersIdeal_eventual_subcritical_representatives_of_numerics
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:29:45.975929+00:00
-- url     : https://prove2.me/submissions/82d7286b-7e89-4cb7-8994-08dcb74f07e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_strict_power_generators
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_subcritical_power_generators
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hnum : LogarithmicInterpolationNumerics m K w v sigma)
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real)) :
    ∃ δ : Real, 0 < δ ∧ δ < (R : Real) ∧
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ∀ P : MvPolynomial (Fin (m + 1)) Complex,
          ∃ Q : MvPolynomial (Fin (m + 1)) Complex,
            P - Q ∈ (logarithmicCentersIdeal c (fun _ => e 0) e) ^ n ∧
            ∀ a ∈ Q.support,
              ∑ i, (w i : Real) * (a i : Real) ≤ (n : Real) * δ := by
  classical
  let I := logarithmicCentersIdeal c (fun _ => e 0) e
  have hdist : ∀ j₁ j₂ : Fin K, j₁ ≠ j₂ → c j₁ ≠ c j₂ := by
    intro j₁ j₂ hne hEq
    let i : Fin m := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hnum.m_pos⟩
    exact hne (hc i (congrFun hEq i))
  have hfinite : FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ I) :=
    logarithmicCentersIdeal_finiteColength c (fun _ => e 0) e he hdist
  obtain ⟨s, D, hD, hgen⟩ :=
    logarithmicCentersIdeal_strict_power_generators
      c hc w v sigma hnum R e hR he hscale
  let B : Set (MvPolynomial (Fin (m + 1)) Complex) :=
    {p | p ∈ I ^ s ∧
      ∀ a ∈ p.support, ∑ i, (w i : Real) * (a i : Real) ≤ (D : Real)}
  have hgen' : I ^ s = Ideal.span B := hgen
  -- A negative cutoff allows only the zero polynomial, so s cannot be zero.
  have hs : 0 < s := by
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    have hDneg : (D : Real) < 0 := by
      simpa [hs0] using hD
    have hB : Ideal.span B = ⊥ := by
      apply Ideal.span_eq_bot.mpr
      intro p hp
      apply MvPolynomial.support_eq_empty.mp
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hnonneg : 0 ≤ ∑ i, (w i : Real) * (a i : Real) :=
        Finset.sum_nonneg (fun i _ =>
          mul_nonneg (hnum.degree_pos i).le (Nat.cast_nonneg (a i)))
      exact (not_lt_of_ge (hnonneg.trans (hp.2 a ha))) hDneg
    have htop : (⊤ : Ideal (MvPolynomial (Fin (m + 1)) Complex)) = ⊥ := by
      simpa [hs0] using hgen'.trans hB
    exact top_ne_bot htop
  -- Noetherianity extracts finitely many of the bounded generators.
  have hfg : (Submodule.span (MvPolynomial (Fin (m + 1)) Complex) B).FG :=
    IsNoetherian.noetherian _
  obtain ⟨S, hSB, hspanS⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset B).mp hfg
  have hspan : Ideal.span (S : Set (MvPolynomial (Fin (m + 1)) Complex)) = I ^ s :=
    hspanS.symm.trans hgen'.symm
  have hweights :
      InterpolationMatrix.columnWeights (w 0 : Real) (fun i => (w i.succ : Real)) =
        (fun i => (w i : Real)) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hdeg : ∀ p ∈ S, ∀ a ∈ p.support,
      ∑ i, InterpolationMatrix.columnWeights (w 0 : Real)
        (fun j => (w j.succ : Real)) i * (a i : Real) ≤ (D : Real) := by
    intro p hp a ha
    rw [hweights]
    exact (hSB hp).2 a ha
  have hsreal : (0 : Real) < (s : Real) := by exact_mod_cast hs
  have hRreal : (0 : Real) < (R : Real) := by exact_mod_cast hR
  have hratio : (D : Real) / (s : Real) < (R : Real) :=
    (div_lt_iff₀' hsreal).mpr hD
  obtain ⟨δ, hδlower, hδR⟩ :=
    exists_between (max_lt_iff.mpr ⟨hratio, hRreal⟩)
  have hδ : 0 < δ := lt_of_le_of_lt (le_max_right _ _) hδlower
  have hDδ : (D : Real) < (s : Real) * δ :=
    (div_lt_iff₀' hsreal).mp
      (lt_of_le_of_lt (le_max_left _ _) hδlower)
  obtain ⟨n0, hn0⟩ :=
    eventual_representatives_of_subcritical_power_generators
      (w 0 : Real) (fun i => (w i.succ : Real))
      (hnum.degree_pos 0) (fun i => hnum.degree_pos i.succ)
      I hfinite δ hδ s hs (D : Real) hDδ S hspan hdeg
  refine ⟨δ, hδ, hδR, n0, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ⟩ := hn0 n hn P
  refine ⟨Q.val, hQ, ?_⟩
  intro a ha
  have hb := Q.property a ha
  rw [hweights] at hb
  exact hb
