-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.formalJet_homogeneous_correction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T06:23:34.804537+00:00
-- url     : https://prove2.me/submissions/54726226-bf0f-4257-bef1-f39a686f0ecf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Finsupp.Weight
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_homogeneous_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : Nat}
    (center : Fin m -> Complex)
    (n : Nat)
    (d : (Fin (m + 1) -> Nat) -> Complex)
    (hzero : (e : Fin (m + 1) -> Nat) ->
      (∑ k : Fin (m + 1), e k) ≠ n -> d e = 0) :
    Exists fun R : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        (∑ k : Fin (m + 1), e k) <= n ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center R) = d e := by
  classical
  let f : Finsupp (Fin (m + 1)) Nat -> Complex :=
    fun a => d (fun k => a k)
  have hdeg (a : Finsupp (Fin (m + 1)) Nat) (ha : f a ≠ 0) :
      (∑ k : Fin (m + 1), a k) = n := by
    by_contra hne
    exact ha (hzero (fun k => a k) hne)
  have hf : (Function.support f).Finite := by
    refine (Finsupp.finite_of_degree_eq (σ := Fin (m + 1)) n).subset ?_
    intro a ha
    change a.degree = n
    rw [Finsupp.degree_eq_sum]
    exact hdeg a ha
  let Q : MvPolynomial (Fin (m + 1)) Complex :=
    AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite f hf)
  have hcoeff (a : Finsupp (Fin (m + 1)) Nat) :
      MvPolynomial.coeff a Q = f a := by
    rfl
  have hhom : ∀ a : Finsupp (Fin (m + 1)) Nat,
      a ∈ Q.support -> (∑ k : Fin (m + 1), a k) = n := by
    intro a ha
    apply hdeg a
    rw [← hcoeff a]
    exact MvPolynomial.mem_support_iff.mp ha
  refine ⟨MvPolynomial.aeval
    (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
      (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
        (MvPolynomial.X 0 - MvPolynomial.C 1))) Q, ?_⟩
  intro e he
  exact
    (OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_homogeneous_coeff
      center n Q hhom e he).trans
        (hcoeff (Finsupp.equivFunOnFinite.symm e))