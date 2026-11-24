-- Prove2me | solution 1 for MvPolyContDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:26:34.133173+00:00
-- url     : https://prove2.me/submissions/1d006c78-538d-4c04-9980-090b8ce4b69c

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k
      (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) := by
  have hA : AnalyticOnNhd ℝ (fun v : Fin n → ℝ => MvPolynomial.eval v P) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial P
  have h1 : ContDiff ℝ k (fun v : Fin n → ℝ => MvPolynomial.eval v P) := by
    rw [← contDiffOn_univ]; exact hA.contDiffOn_of_completeSpace
  exact h1.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
