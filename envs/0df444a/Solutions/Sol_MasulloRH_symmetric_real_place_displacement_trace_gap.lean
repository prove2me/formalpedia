-- Prove2me | solution 1 for MasulloRH.symmetric_real_place_displacement_trace_gap
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:23:44.658855+00:00
-- url     : https://prove2.me/submissions/457deaa4-a81d-4fd9-842a-bd9c3d248aac

import Mathlib
open Real

theorem solution (M h : ℝ) (c : ℕ → ℝ) (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hc : ∀ n, 0 ≤ c n) (h0 : 3*M ≤ c 0)
    (hp : Summable (fun n : ℕ => c n * exp (-((9/2 : ℝ)+2*n)*h)))
    (hn : Summable (fun n : ℕ => c n * exp (-((9/2 : ℝ)+2*n)*(-h)))) :
    let W := fun u : ℝ => exp (u/2)*M + (exp (2*u)-1)*
      ∑' n : ℕ, c n * exp (-((9/2 : ℝ)+2*n)*u)
    W 0 = M ∧
    (W h + W (-h))/2 = cosh (h/2)*M -
      ∑' n : ℕ, 2*c n*sinh h*sinh (((7/2 : ℝ)+2*n)*h) ∧
    (W h + W (-h))/2 ≤ M - (167/8 : ℝ)*M*h^2 := by
  intro W
  have lowS (x : ℝ) (hx : 0 ≤ x) : x ≤ sinh x := by
    simpa using le_hasSum (Real.hasSum_sinh x) 0 (by intro j hj; positivity)
  have lowC (x : ℝ) (hx : 0 ≤ x) : 1 ≤ cosh x := by
    simpa using le_hasSum (Real.hasSum_cosh x) 0 (by intro j hj; positivity)
  have nscale (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : (n:ℝ)*sinh x ≤ sinh ((n:ℝ)*x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hy : 0 ≤ (n:ℝ)*x := by positivity
      have h1 := mul_nonneg (hy.trans (lowS _ hy)) (sub_nonneg.mpr (lowC x hx))
      have h2 := mul_nonneg (sub_nonneg.mpr (lowC _ hy)) (hx.trans (lowS x hx))
      push_cast
      simp only [add_mul,one_mul,Real.sinh_add]
      linarith
  have qpos : 0 ≤ h/4 := by positivity
  have h4 : 4*sinh (h/4) ≤ sinh h := by convert nscale (h/4) qpos 4 using 1 <;> norm_num <;> ring_nf
  have h14 : 14*sinh (h/4) ≤ sinh (7*h/2) := by convert nscale (h/4) qpos 14 using 1 <;> norm_num <;> ring_nf
  have non4 := qpos.trans (lowS _ qpos)
  have b1 := mul_le_mul h4 h14 (by positivity) (hh.trans (lowS _ hh))
  have b2 := mul_le_mul (lowS h hh) (lowS (7*h/2) (by positivity)) (by positivity) (hh.trans (lowS _ hh))
  have hyp : cosh (h/2) = 2*sinh (h/4)^2+1 := by
    rw [show h/2 = 2*(h/4) by ring, Real.cosh_two_mul,Real.cosh_sq]
    ring
  have sharp : (167/8:ℝ)*h^2 ≤ 6*sinh h*sinh (7*h/2)-(cosh (h/2)-1) := by
    rw [hyp]
    nlinarith only [b1,b2]
  let A := fun n : ℕ => (9/2 : ℝ)+2*n
  let B := fun n : ℕ => 2*c n*sinh h*sinh (((7/2 : ℝ)+2*n)*h)
  let F := fun (u : ℝ) (n : ℕ) => c n * exp (-(A n)*u)
  have sumPair := (hp.hasSum.mul_left (exp (2*h)-1)).add (hn.hasSum.mul_left (exp (2*(-h))-1))
  have pair (n : ℕ) :
      (exp (2*h)-1) * F h n + (exp (2*(-h))-1) * F (-h) n = -2*B n := by
    let a := A n
    have p (y : ℝ) : (exp (2*y)-1) * F y n = c n*(exp ((2-a)*y)-exp (-a*y)) := by
      change (exp (2*y)-1)*(c n*exp (-a*y)) = _
      rw [show (2-a)*y = 2*y+(-a*y) by ring, Real.exp_add]
      ring
    rw [p,p]
    have coshPair (b : ℝ) : exp (b*h) + exp (b*(-h)) = 2*cosh (b*h) := by
      rw [Real.cosh_eq,show b*(-h) = -(b*h) by ring]; ring
    calc
      _ = c n*((exp ((2-a)*h)+exp ((2-a)*(-h)))-(exp (-a*h)+exp (-a*(-h)))) := by ring
      _ = 2*c n*(cosh ((2-a)*h) - cosh (-a*h)) := by rw [coshPair,coshPair]; ring
      _ = _ := by
        rw [show (2-a)*h = -((a-1)*h-h) by ring,show -a*h = -((a-1)*h+h) by ring,
          Real.cosh_neg,Real.cosh_neg,Real.cosh_sub,Real.cosh_add]
        change _ = -2*(2*c n*sinh h*sinh (((7/2 : ℝ)+2*n)*h))
        dsimp [a,A]
        ring_nf
  have sB : HasSum B (-((exp (2*h)-1)*(∑' n, F h n)+(exp (2*(-h))-1)*(∑' n, F (-h) n))/2) := by
    let t := (exp (2*h)-1)*(∑' n, F h n)+(exp (2*(-h))-1)*(∑' n, F (-h) n)
    change HasSum B (-t/2)
    have eql : B = fun n => -(1/2:ℝ)*((exp (2*h)-1)*F h n+(exp (2*(-h))-1)*F (-h) n) := by
      funext n
      rw [pair]; ring
    rw [eql,show -t/2 = -(1/2:ℝ)*t by ring]
    exact sumPair.mul_left (-(1/2:ℝ))
  have mean : (W h + W (-h))/2 = cosh (h/2)*M - ∑' n, B n := by
    rw [sB.tsum_eq,Real.cosh_eq]
    dsimp [W,F,A]
    rw [show -(h/2) = (-h)/2 by ring]
    ring
  refine ⟨by simp [W],mean,?_⟩
  have nonB (n : ℕ) : 0 ≤ B n := by
    have harg : 0 ≤ ((7/2 : ℝ)+2*n)*h := by positivity
    exact mul_nonneg (mul_nonneg (by have := hc n; positivity) (hh.trans (lowS _ hh))) (harg.trans (lowS _ harg))
  have b0 := le_hasSum sB 0 (fun i _ => nonB i)
  rw [← sB.tsum_eq] at b0
  have big := mul_nonneg (sub_nonneg.mpr h0) (mul_nonneg (hh.trans (lowS _ hh))
    (show 0 ≤ sinh (7*h/2) from (by positivity : 0 ≤ 7*h/2).trans (lowS _ (by positivity))))
  have msharp := mul_nonneg hM (sub_nonneg.mpr sharp)
  rw [mean]
  dsimp [B] at b0
  norm_num at b0
  rw [show (7/2 : ℝ)*h = 7*h/2 by ring] at b0
  nlinarith only [b0,big,msharp]
