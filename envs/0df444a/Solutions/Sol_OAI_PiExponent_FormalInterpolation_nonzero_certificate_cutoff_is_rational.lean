-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.nonzero_certificate_cutoff_is_rational
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:59:36.848335+00:00
-- url     : https://prove2.me/submissions/d19d6e04-6d65-4049-8117-c1f63f015643

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (hd : 0 < d) (w : Fin d → Rat) (D : Real)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : Real)) D (f j)))) :
    ∃ q : Rat, (q : Real) = D := by
  by_contra hnot
  have hnot' : ¬ ∃ q : Rat, (q : Real) = D := hnot
  have hweight (α : Fin d →₀ Nat) :
      ∃ q : Rat, (q : Real) = Finsupp.weight (fun k => (w k : Real)) α := by
    refine ⟨∑ k, (α k : Rat) * w k, ?_⟩
    rw [Finsupp.weight_apply,
      α.sum_fintype (fun i c => c • (w i : Real)) (fun _ => zero_smul _ _)]
    simp [smul_eq_mul]
  have hzero (j : Fin n) :
      MvPolynomial.weightedHomogeneousComponent
        (fun k => (w k : Real)) D (f j) = 0 := by
    apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
    intro α hα
    have hcoeff : MvPolynomial.coeff α (f j) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hα
    obtain ⟨q, hq⟩ := hweight α
    intro hD
    exact hnot' ⟨q, hq.trans hD⟩
  obtain ⟨i, _⟩ : ∃ i : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨e, he, hmem⟩ := hgen i
  rw [Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  simp only [hzero, mul_zero, Finset.sum_const_zero] at hc
  exact (pow_ne_zero e (MvPolynomial.X_ne_zero i)) hc.symm