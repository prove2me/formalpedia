-- Prove2me | solution 1 for LatinQuarter.coeff_prod_add_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:25.399626+00:00
-- url     : https://prove2.me/submissions/96f7cc34-8828-44d4-ab83-8321820660e4

module
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.tag_sq

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {ι κ : Type*} [Fintype ι]
    (f : ι → κ) (a : ι → ZMod 2) (d : κ →₀ ℕ)
    (hd : ∑ j ∈ d.support, d j = Fintype.card ι) :
    (∏ i, (X (f i) + C (a i))).coeff d = (∏ i, X (f i) : MvPolynomial κ (ZMod 2)).coeff d := by
  classical
  rw [Fintype.prod_add, coeff_sum]
  rw [Finset.sum_eq_single (Finset.univ : Finset ι)]
  · simp
  · intro s _ hs
    apply coeff_eq_zero_of_totalDegree_lt
    have hc : s.card < Fintype.card ι := by
      exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hs)
    have hdeg : (∏ i ∈ s, (X (f i) : MvPolynomial κ (ZMod 2))).totalDegree ≤ s.card := by
      simpa using totalDegree_finsetProd s (fun i => (X (f i) : MvPolynomial κ (ZMod 2)))
    have hconst : (∏ i ∈ sᶜ, C (a i) : MvPolynomial κ (ZMod 2)).totalDegree = 0 := by
      rw [← map_prod]
      exact totalDegree_C _
    have hm := totalDegree_mul (∏ i ∈ s, (X (f i) : MvPolynomial κ (ZMod 2)))
      (∏ i ∈ sᶜ, C (a i))
    rw [hconst, add_zero] at hm
    rw [hd]
    exact lt_of_le_of_lt (hm.trans hdeg) hc
  · simp
end LatinQuarter
