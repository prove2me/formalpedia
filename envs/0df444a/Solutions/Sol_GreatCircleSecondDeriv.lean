-- Prove2me | solution 1 for GreatCircleSecondDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:37.842512+00:00
-- url     : https://prove2.me/submissions/de0c941b-6a42-41f9-953d-7b5d553b7849

module
public import Definitions.Def_PHarmonicPoly_MvPolyHessian
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradient
public import Theorems.Thm_MvPolyHessian


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (C A B : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) i) P) t
      = iteratedFDeriv ℝ 2
          (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
          (C + Real.cos t • A + Real.sin t • B)
          ![-Real.sin t • A + Real.cos t • B, -Real.sin t • A + Real.cos t • B]
        - inner ℝ
            (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P)
              (C + Real.cos t • A + Real.sin t • B))
            (Real.cos t • A + Real.sin t • B) := by
  have hcurve : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => (C + Real.cos r • A + Real.sin r • B : EuclideanSpace ℝ (Fin n)))
      ((-Real.sin s) • A + Real.cos s • B) s := by
    intro s
    have hval : ((0 : EuclideanSpace ℝ (Fin n)) + (-Real.sin s) • A + Real.cos s • B)
        = ((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) := by
      rw [zero_add]
    exact hval ▸ (((hasDerivAt_const s (C : EuclideanSpace ℝ (Fin n))).add
      ((Real.hasDerivAt_cos s).smul_const A)).add
      ((Real.hasDerivAt_sin s).smul_const B))
  have hcurve2 : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => ((-Real.sin r) • A + Real.cos r • B : EuclideanSpace ℝ (Fin n)))
      ((-Real.cos s) • A + (-Real.sin s) • B) s := by
    intro s
    exact ((Real.hasDerivAt_sin s).neg.smul_const A).add
      ((Real.hasDerivAt_cos s).smul_const B)
  have hchain : ∀ (Q : MvPolynomial (Fin n) ℝ) (s : ℝ), HasDerivAt
      (fun r : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos r • A + Real.sin r • B : EuclideanSpace ℝ (Fin n)) i) Q)
      (∑ i, MvPolynomial.eval
          (fun j => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) j)
          (pderiv i Q) *
        (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i)) s := by
    intro Q s
    have h := HasFDerivAt.comp_hasDerivAt s
      (MvPolyFDerivEuclidean Q (C + Real.cos s • A + Real.sin s • B)) (hcurve s)
    have hval : (∑ i, (MvPolynomial.eval
          (fun j => (C + Real.cos s • A + Real.sin s • B
            : EuclideanSpace ℝ (Fin n)) j) (pderiv i Q)) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
        ((-Real.sin s) • A + Real.cos s • B)
        = ∑ i, MvPolynomial.eval
            (fun j => (C + Real.cos s • A + Real.sin s • B
              : EuclideanSpace ℝ (Fin n)) j) (pderiv i Q) *
          (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i) := by
      simp
    exact hval ▸ h
  have hderiv1 : deriv (fun r : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos r • A + Real.sin r • B : EuclideanSpace ℝ (Fin n)) i) P)
      = fun s : ℝ => ∑ i, MvPolynomial.eval
          (fun j => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) j)
          (pderiv i P) *
        (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i) := by
    funext s
    exact (hchain P s).deriv
  have hcoord : ∀ i : Fin n, HasDerivAt
      (fun s : ℝ => (((-Real.sin s) • A + Real.cos s • B
        : EuclideanSpace ℝ (Fin n)) i))
      (((-Real.cos t) • A + (-Real.sin t) • B : EuclideanSpace ℝ (Fin n)) i) t := by
    intro i
    exact HasFDerivAt.comp_hasDerivAt t
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt)
      (hcurve2 t)
  have hterm : ∀ i : Fin n, HasDerivAt
      (fun s : ℝ => MvPolynomial.eval
          (fun j => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) j)
          (pderiv i P) *
        (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i))
      ((∑ j, MvPolynomial.eval
            (fun k => (C + Real.cos t • A + Real.sin t • B
              : EuclideanSpace ℝ (Fin n)) k)
            (pderiv j (pderiv i P)) *
          (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) j)) *
          (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) i)
        + MvPolynomial.eval
            (fun j => (C + Real.cos t • A + Real.sin t • B
              : EuclideanSpace ℝ (Fin n)) j) (pderiv i P) *
          (((-Real.cos t) • A + (-Real.sin t) • B : EuclideanSpace ℝ (Fin n)) i)) t :=
    fun i => (hchain (pderiv i P) t).mul (hcoord i)
  have hfe : (∑ i, fun s : ℝ => MvPolynomial.eval
        (fun j => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) j)
        (pderiv i P) *
      (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i))
      = fun s : ℝ => ∑ i, MvPolynomial.eval
        (fun j => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) j)
        (pderiv i P) *
      (((-Real.sin s) • A + Real.cos s • B : EuclideanSpace ℝ (Fin n)) i) := by
    funext s
    simp
  have hsum2 := hfe ▸ HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hiter : iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
      (fun i => (C + Real.cos s • A + Real.sin s • B : EuclideanSpace ℝ (Fin n)) i) P) t
      = deriv (deriv (fun s : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos s • A + Real.sin s • B
          : EuclideanSpace ℝ (Fin n)) i) P)) t := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter, hderiv1, hsum2.deriv]
  have hginner : (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
        MvPolynomial.eval (fun i => y i) P)
        (C + Real.cos t • A + Real.sin t • B))
      (Real.cos t • A + Real.sin t • B) : ℝ)
      = ∑ i, MvPolynomial.eval
          (fun j => (C + Real.cos t • A + Real.sin t • B
            : EuclideanSpace ℝ (Fin n)) j) (pderiv i P) *
        ((Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) := by
    rw [MvPolyGradient P (C + Real.cos t • A + Real.sin t • B), PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [MvPolyHessian P (C + Real.cos t • A + Real.sin t • B) _ _, hginner]
  have hA2 : (∑ i, (∑ j, MvPolynomial.eval
          (fun k => (C + Real.cos t • A + Real.sin t • B
            : EuclideanSpace ℝ (Fin n)) k) (pderiv j (pderiv i P)) *
        (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) j)) *
        (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) i))
      = ∑ i, ∑ j,
        (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) i) *
        (((-Real.sin t) • A + Real.cos t • B : EuclideanSpace ℝ (Fin n)) j) *
        MvPolynomial.eval
          (fun k => (C + Real.cos t • A + Real.sin t • B
            : EuclideanSpace ℝ (Fin n)) k) (pderiv i (pderiv j P)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hB2 : (∑ i, MvPolynomial.eval
        (fun j => (C + Real.cos t • A + Real.sin t • B
          : EuclideanSpace ℝ (Fin n)) j) (pderiv i P) *
      (((-Real.cos t) • A + (-Real.sin t) • B : EuclideanSpace ℝ (Fin n)) i))
      = -∑ i, MvPolynomial.eval
        (fun j => (C + Real.cos t • A + Real.sin t • B
          : EuclideanSpace ℝ (Fin n)) j) (pderiv i P) *
      ((Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hh : (((-Real.cos t) • A + (-Real.sin t) • B : EuclideanSpace ℝ (Fin n)) i)
        = -((Real.cos t • A + Real.sin t • B : EuclideanSpace ℝ (Fin n)) i) := by
      simp
      ring
    rw [hh]
    ring
  rw [Finset.sum_add_distrib, hA2, hB2]
  ring
