-- Prove2me | solution 1 for GlobalSinkhorn.product_bounds_of_radius
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:31:58.279164+00:00
-- url     : https://prove2.me/submissions/62013281-0b29-418b-bbb6-19a167ce3862

import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
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

theorem solution {n : ℕ} (hn : 2 ≤ n) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hB : B ∈ doublyStochastic ℝ (Fin n))
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y) :
    ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y ∧ (⨅ i, x i) = (⨅ j, y j) ∧
      ∀ i j, Real.exp (-(2 * scalingRadius A B)) ≤ x i * y j ∧
        x i * y j ≤ Real.exp (2 * scalingRadius A B) := by
  classical
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  obtain ⟨u, v, huv, hnorm⟩ := minimum_radius A B hAB
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  let c : ℝ := -(u i₀ + v j₀) / 2
  let x : Fin n → ℝ := fun i => Real.exp (u i + c)
  let y : Fin n → ℝ := fun j => Real.exp (-(v j + c))
  have hprod : ∀ i j, x i * y j = Real.exp (u i - v j) := by
    intro i j
    dsimp [x, y]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨x, y, ⟨fun i => Real.exp_pos _, fun j => Real.exp_pos _, ?_⟩, ?_, ?_⟩
  · ext i j
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) huv
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he ⊢
    calc
      B i j = Real.exp (u i) * A i j * Real.exp (-v j) := he
      _ = (Real.exp (u i) * Real.exp (-v j)) * A i j := by ring
      _ = (x i * y j) * A i j := by rw [hprod, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
      _ = x i * A i j * y j := by ring
  · have hxmin : (⨅ i, x i) = x i₀ := by
      apply le_antisymm
      · exact ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact (Real.exp_pos _).le⟩ i₀
      · apply le_ciInf
        intro i
        apply Real.exp_le_exp.mpr
        have hi := hmin i (Finset.mem_univ i)
        linarith
    have hymin : (⨅ j, y j) = y j₀ := by
      apply le_antisymm
      · exact ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact (Real.exp_pos _).le⟩ j₀
      · apply le_ciInf
        intro j
        apply Real.exp_le_exp.mpr
        have := hmax j (Finset.mem_univ j)
        dsimp [c]
        linarith
    rw [hxmin, hymin]
    apply congrArg Real.exp
    dsimp [c]
    ring
  · intro i j
    have hui : |u i| ≤ scalingRadius A B := by
      calc
        |u i| = ‖u i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖u‖ := norm_le_pi_norm u i
        _ ≤ max ‖u‖ ‖v‖ := le_max_left _ _
        _ = scalingRadius A B := hnorm
    have hvj : |v j| ≤ scalingRadius A B := by
      calc
        |v j| = ‖v j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖v‖ := norm_le_pi_norm v j
        _ ≤ max ‖u‖ ‖v‖ := le_max_right _ _
        _ = scalingRadius A B := hnorm
    rw [hprod]
    constructor <;> apply Real.exp_le_exp.mpr <;> obtain ⟨hu₁, hu₂⟩ := abs_le.mp hui <;>
      obtain ⟨hv₁, hv₂⟩ := abs_le.mp hvj <;> linarith

#print axioms solution


