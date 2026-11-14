-- Prove2me | solution 1 for GlobalSinkhorn.scalingRadius_attained
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:22:40.607646+00:00
-- url     : https://prove2.me/submissions/97517560-08e1-4a3b-baa0-c8bdc4958370

import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_scalingRadius
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Matrix
open GlobalSinkhorn
open scoped BigOperators

private lemma minimum_radius {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y) :
    ∃ u v : Fin n → ℝ,
      B = Matrix.diagonal (fun i => Real.exp (u i)) * A *
          Matrix.diagonal (fun j => Real.exp (-v j)) ∧
        max ‖u‖ ‖v‖ = scalingRadius A B := by
  classical
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | ∀ i j, B i j = Real.exp (p.1 i) * A i j * Real.exp (-p.2 j)}
  have hclosed : IsClosed F := by
    change IsClosed {p : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i j,
      B i j = Real.exp (p.1 i) * A i j * Real.exp (-p.2 j)}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    exact isClosed_eq continuous_const (by fun_prop)
  obtain ⟨x, y, hx, hy, hxy⟩ := hAB
  let p₀ : (Fin n → ℝ) × (Fin n → ℝ) := (fun i => Real.log (x i), fun j => -Real.log (y j))
  have hp₀ : p₀ ∈ F := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hxy
    simpa [p₀, Matrix.diagonal_mul, Matrix.mul_diagonal, Real.exp_log (hx i), Real.exp_log (hy j)] using h
  have hcompact : IsCompact (Metric.closedBall 0 ‖p₀‖ ∩ F) :=
    (isCompact_closedBall 0 ‖p₀‖).inter_right hclosed
  have hne : (Metric.closedBall 0 ‖p₀‖ ∩ F).Nonempty :=
    ⟨p₀, by simp [hp₀]⟩
  obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hne continuous_norm.continuousOn
  have hminall : ∀ q ∈ F, ‖p‖ ≤ ‖q‖ := by
    intro q hq
    by_cases hb : q ∈ Metric.closedBall 0 ‖p₀‖
    · exact hmin ⟨hb, hq⟩
    · have hpbound : ‖p‖ ≤ ‖p₀‖ := by simpa using hp.1
      have hqbound : ‖p₀‖ < ‖q‖ := by simpa using hb
      exact hpbound.trans hqbound.le
  have hpeq : B = Matrix.diagonal (fun i => Real.exp (p.1 i)) * A *
      Matrix.diagonal (fun j => Real.exp (-p.2 j)) := by
    ext i j
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using hp.2 i j
  refine ⟨p.1, p.2, hpeq, ?_⟩
  symm
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨p.1, p.2, hpeq, rfl⟩
  · intro r hr
    obtain ⟨u, v, huv, rfl⟩ := hr
    have hq : (u, v) ∈ F := by
      intro i j
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) huv
      simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using h
    exact hminall (u, v) hq

theorem solution {n : ℕ} (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hB : B ∈ doublyStochastic ℝ (Fin n))
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y) :
    ∃ u v : Fin n → ℝ,
      B = Matrix.diagonal (fun i => Real.exp (u i)) * A *
          Matrix.diagonal (fun j => Real.exp (-v j)) ∧
        max ‖u‖ ‖v‖ = scalingRadius A B := by
  exact minimum_radius A B hAB

#print axioms solution
