-- Prove2me | solution 1 for LeanPool.CencovPetz.fisherBilin_pushforward_le_of_markovMorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:02.829844+00:00
-- url     : https://prove2.me/submissions/e8fc24cd-1f28-40a3-9029-7354f1d53387

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
namespace LeanPool.CencovPetz
theorem _root_.solution (κ : MarkovMorphism α β)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (κ.pushforward p) (κ.tangentPushforward u) (κ.tangentPushforward u) ≤
      fisherBilin p u u := by
  classical
  -- Expand both sides.
  simp only [fisherBilin.apply, MarkovMorphism.pushforward_apply,
    MarkovMorphism.tangentPushforward_apply]
  -- It suffices to prove the inequality termwise in `b` and sum.
  have hb (b : β) :
      ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
            (∑ a : α, p.p a * κ.K a b)
        ≤ ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    -- Cauchy–Schwarz in “Engel form” on the finite index set `α`.
    have hf (a : α) : 0 ≤ (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b := by
      have hp_pos : 0 < p.p a := p.pos a
      have : 0 ≤ (((u : α → ℝ) a) ^ 2) / p.p a :=
        div_nonneg (sq_nonneg _) (le_of_lt hp_pos)
      exact mul_nonneg this (κ.nonneg a b)
    have hg (a : α) : 0 ≤ p.p a * κ.K a b :=
      mul_nonneg (p.pos a).le (κ.nonneg a b)
    have ht (a : α) :
        (((u : α → ℝ) a) * κ.K a b) ^ 2 =
          ((((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b) * (p.p a * κ.K a b) := by
      -- Expand and cancel `p.p a`.
      have hp_ne : p.p a ≠ 0 := ne_of_gt (p.pos a)
      -- `^2` is `pow_two`.
      -- We keep the proof `simp`-driven (upstream-friendly).
      simp [pow_two, div_eq_mul_inv, hp_ne, mul_assoc, mul_left_comm, mul_comm]
    have hcs :
        (∑ a : α, (u : α → ℝ) a * κ.K a b) ^ 2
          ≤ (∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b) * (∑ a : α, p.p a * κ.K a b) := by
      -- Use the finset lemma on `Finset.univ`.
      simpa using
        (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset α))
          (r := fun a => (u : α → ℝ) a * κ.K a b)
          (f := fun a => (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b)
          (g := fun a => p.p a * κ.K a b)
          (fun a _ => hf a) (fun a _ => hg a) (fun a _ => le_of_eq (ht a)))
    have hden_pos : 0 < ∑ a : α, p.p a * κ.K a b := by
      rcases κ.col_pos b with ⟨a0, ha0⟩
      have h_nonneg' : ∀ a : α, 0 ≤ p.p a * κ.K a b := hg
      -- One term is positive.
      refine Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => p.p a * κ.K a b) (h := fun a _ => h_nonneg' a) ?_
      exact ⟨a0, by simp, mul_pos (p.pos a0) ha0⟩
    -- Divide the Cauchy–Schwarz inequality by the (positive) denominator.
    have hdiv :
        ((∑ a : α, (u : α → ℝ) a * κ.K a b) ^ 2) / (∑ a : α, p.p a * κ.K a b)
          ≤ ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a * κ.K a b :=
      (div_le_iff₀ hden_pos).2 (by simpa [mul_assoc] using hcs)
    -- Rewrite `x^2` as `x*x` and align `u^2` with `u*u`.
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiv
  -- Sum over `b`.
  have hsum :
      (∑ b : β,
            ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
              (∑ a : α, p.p a * κ.K a b))
        ≤ ∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    simpa using (Finset.sum_le_sum fun b _ => hb b)
  -- Swap sums on the right and use row-stochasticity.
  have hcomm :
      (∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b)
        = ∑ a : α, ∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset β)) (t := (Finset.univ : Finset α))
        (f := fun b a => (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b))
  calc
    (∑ b : β,
          ((∑ a : α, (u : α → ℝ) a * κ.K a b) * ∑ a : α, (u : α → ℝ) a * κ.K a b) /
            (∑ a : α, p.p a * κ.K a b))
        ≤ ∑ b : β, ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := hsum
    _ = ∑ a : α, ∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b := hcomm
    _ = ∑ a : α, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a := by
          -- Pull the `a`-dependent coefficient out and use `∑_b K(a,b) = 1`.
          refine Finset.sum_congr rfl (fun a _ => ?_)
          have :
              (∑ b : β, (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * κ.K a b)
                = (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a * (∑ b : β, κ.K a b) := by
            -- `∑ (f b * c) = (∑ f b) * c`.
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Finset.sum_mul (s := (Finset.univ : Finset β)) (f := fun b => κ.K a b)
                (a := (((u : α → ℝ) a) * (u : α → ℝ) a) / p.p a)).symm
          simp [this, κ.row_sum_eq_one a]
    _ = ∑ a : α, ((u : α → ℝ) a * (u : α → ℝ) a) / p.p a := rfl
end LeanPool.CencovPetz
