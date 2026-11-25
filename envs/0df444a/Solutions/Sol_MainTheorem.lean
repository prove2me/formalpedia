-- Prove2me | solution 1 for MainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:17:48.235884+00:00
-- url     : https://prove2.me/submissions/293d92a0-f274-4fd8-8cdb-a58efa77e98d

module
public import Definitions.Def_PHarmonicPoly_HomogeneousCase
public import Definitions.Def_PHarmonicPoly_TopComponent
public import Definitions.Def_PHarmonicPoly_TopComponentNeZero
public import Definitions.Def_PHarmonicPoly_AffineOfTotalDegreeLeOne
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_MainTheorem
public import Theorems.Thm_AffineOfTotalDegreeLeOne
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_HomogeneousCase
public import Theorems.Thm_TopComponent
public import Theorems.Thm_TopComponentNeZero


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c := by
  have halg : EpAlg p P = 0 := by
    refine MvPolynomial.funext (fun v => ?_)
    have hx := hE (WithLp.toLp 2 v)
    rw [EpOpEvalPoly p P (WithLp.toLp 2 v)] at hx
    simpa using hx
  rcases le_or_gt P.totalDegree 1 with hd | hd
  · exact AffineOfTotalDegreeLeOne hd
  · exfalso
    have hP : P ≠ 0 := by
      intro h
      rw [h] at hd
      simp at hd
    exact HomogeneousCase hn hd hp (TopComponentNeZero hP)
      (MvPolynomial.homogeneousComponent_isHomogeneous _ _) (TopComponent p hd halg)
