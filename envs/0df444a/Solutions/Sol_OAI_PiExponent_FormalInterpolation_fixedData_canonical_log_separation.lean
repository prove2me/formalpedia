-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:52:27.561839+00:00
-- url     : https://prove2.me/submissions/484bcf99-6100-43d1-8155-7b2f08842c86

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_log_products_separated_of_growth

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ A B : Finset (Fin (d.m + 1)), A.card = B.card →
       ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
         (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
           interpolationSeparationConstant d.m d.sigma * (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real)) := by
  let x : Nat → Real := d.x
  let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
  let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
  have hx0 : x 0 = 1 := d.x_zero
  have hxle : ∀ n, n ≤ d.m → 1 ≤ x n := by
    intro n hn
    exact d.x_one_le n
  have hgrowth : ∀ n, 1 ≤ n → n ≤ d.m →
      (interpolationSeparationConstant d.m d.sigma *
        (max 1 (max (d.v0 : Real) (1 / (d.base.theta : Real)) / min (d.w0 : Real) 1)) ^ (d.m + 1)) *
        (∏ j ∈ Finset.range n, x j) < x n := by
    intro n hn1 hn
    simpa [OAI.PiExponentApprox.weightSeparationFactor, x] using
      d.weight_growth n hn1 hn
  have hmain := OAI.PiExponent.FormalInterpolation.canonical_log_products_separated_of_growth
    d.m x (d.w0 : Real) (d.v0 : Real) (d.base.theta : Real)
    (interpolationSeparationConstant d.m d.sigma) hx0 hxle
    d.w0_pos d.v0_pos d.base.theta_pos hgrowth
  have hw (i : Fin (d.m + 1)) :
      (w i : Real) = Fin.cases (d.w0 : Real) (fun j => x (j.val + 1)) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [w, x, d.x_log]
  have hv (i : Fin (d.m + 1)) :
      (v i : Real) =
        Fin.cases (d.v0 : Real) (fun j => x (j.val + 1) / (d.base.theta : Real)) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [v, x, d.x_log, Rat.cast_div]
  dsimp only
  intro A B hcard i hi hiA hiB hagree
  change interpolationSeparationConstant d.m d.sigma *
    (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real)
  calc
    interpolationSeparationConstant d.m d.sigma * (∏ j ∈ B, (v j : Real)) =
        interpolationSeparationConstant d.m d.sigma *
          (∏ j ∈ B, Fin.cases (d.v0 : Real)
            (fun k => x (k.val + 1) / (d.base.theta : Real)) j) := by
      exact congrArg (fun t : Real => interpolationSeparationConstant d.m d.sigma * t)
        (Finset.prod_congr rfl (fun j _ => hv j))
    _ < ∏ j ∈ A, Fin.cases (d.w0 : Real) (fun k => x (k.val + 1)) j :=
      hmain A B hcard i hi hiA hiB hagree
    _ = ∏ j ∈ A, (w j : Real) :=
      Finset.prod_congr rfl (fun j _ => (hw j).symm)