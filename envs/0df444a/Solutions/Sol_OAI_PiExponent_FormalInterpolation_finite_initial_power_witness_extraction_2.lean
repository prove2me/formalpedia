-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.finite_initial_power_witness_extraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T17:15:18.318102+00:00
-- url     : https://prove2.me/submissions/59e167ba-18f6-49e6-8964-719dc133cff6

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

section

open MvPolynomial

namespace PiL14

theorem extract {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : 0 < D)
    (hinitial : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ D}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : Real)) D p.1))) :
    ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
      (∀ j, f j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (f j).support,
        ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
      (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
        MvPolynomial.X i ^ e ∈
          Ideal.span (Set.range (fun j : Fin k =>
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j)))) := by
  classical
  set Sub := {g : MvPolynomial (Fin d) Complex // g ∈ I ^ s ∧ ∀ a ∈ g.support, ∑ j, (w j : Real) * (a j : Real) ≤ D}
  set φ : Sub → MvPolynomial (Fin d) ℂ := fun p => weightedHomogeneousComponent (fun j => (w j : Real)) D p.1
  choose e he hmem using hinitial
  have hfin : ∀ i, ∃ T : Finset (MvPolynomial (Fin d) ℂ), (T : Set _) ⊆ Set.range φ ∧
      X i ^ e i ∈ Ideal.span (T : Set (MvPolynomial (Fin d) ℂ)) := fun i =>
    Submodule.mem_span_finite_of_mem_span (hmem i)
  choose T hTsub hTmem using hfin
  have hpre : ∀ i, ∀ t ∈ T i, ∃ p : Sub, φ p = t := fun i t ht => hTsub i ht
  choose pre hpre' using hpre
  let U : Finset Sub := Finset.univ.biUnion fun i => (T i).attach.image fun t => pre i t.1 t.2
  refine ⟨U.card, fun j => (U.equivFin.symm j).1.1, fun j => (U.equivFin.symm j).1.2.1,
    fun j => (U.equivFin.symm j).1.2.2, fun i => ⟨e i, he i, ?_⟩⟩
  refine Ideal.span_mono ?_ (hTmem i)
  intro t ht
  have hU : pre i t ht ∈ U := by
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
    exact ⟨i, ⟨t, ht⟩, rfl⟩
  refine ⟨U.equivFin ⟨pre i t ht, hU⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hpre' i t ht

end PiL14

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : 0 < D)
    (hinitial : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ D}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : Real)) D p.1))) :
    ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
      (∀ j, f j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (f j).support,
        ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
      (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
        MvPolynomial.X i ^ e ∈
          Ideal.span (Set.range (fun j : Fin k =>
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j)))) := by
  apply PiL14.extract <;> assumption
