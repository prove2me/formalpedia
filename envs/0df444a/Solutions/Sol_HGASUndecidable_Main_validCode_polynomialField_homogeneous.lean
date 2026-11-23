-- Prove2me | solution 1 for HGASUndecidable.Main.validCode_polynomialField_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:19:18.198871+00:00
-- url     : https://prove2.me/submissions/f706b4e4-ac8b-45fc-bc3f-36055d406616

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

private lemma evalQField_scaled_of_support_sum {n d : ℕ}
    (p : QPoly n) (hp : ∀ m ∈ p.support, m.sum (fun _ a => a) = d)
    (a : ℝ) (x : State n) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (a • x) p =
      a ^ d * MvPolynomial.eval₂ (algebraMap ℚ ℝ) x p := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hpow : (∏ i ∈ m.support, (a • x) i ^ m i) =
      a ^ d * ∏ i ∈ m.support, x i ^ m i := by
    change (∏ i ∈ m.support, (a * x i) ^ m i) =
      a ^ d * ∏ i ∈ m.support, x i ^ m i
    simp only [mul_pow, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 2
    simpa [Finsupp.sum] using hp m hm
  rw [hpow]
  ring

private lemma evalQField_scaled (c : RawFieldCode) (hc : ValidCode c)
    (a : ℝ) (x : State c.1) :
    codeField c (a • x) = a ^ c.2.1 • codeField c x := by
  ext i
  simp only [codeField, evalQField]
  exact evalQField_scaled_of_support_sum (codePolys c i) (hc.2.2.2 i) a x

end HGASUndecidable.Main

open HGASUndecidable.Main

theorem solution (c : RawFieldCode) (hc : ValidCode c) :
    PolynomialField (codeField c) ∧ Homogeneous c.2.1 (codeField c) := by
  constructor
  · refine ⟨fun i => MvPolynomial.map (algebraMap ℚ ℝ) (codePolys c i), ?_⟩
    funext x
    ext i
    simp [codeField, evalQField, evalField, MvPolynomial.eval_map]
  · intro a ha x
    exact HGASUndecidable.Main.evalQField_scaled c hc a x
