-- Prove2me | solution 1 for MarkovMixing.network_walk_reversible
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:25:50.362305+00:00
-- url     : https://prove2.me/submissions/ebf3d048-4168-4fa1-b141-66f1b4b92223

import Definitions.Def_mm_network
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x) :
    IsStochastic (networkWalk c) ∧
    DetailedBalance (networkWalk c)
      (fun x => vertexConductance c x / totalConductance c) ∧
    IsStationary (networkWalk c)
      (fun x => vertexConductance c x / totalConductance c) := by
  classical
  have hentry : ∀ x y : V, networkWalk c x y = c x y / vertexConductance c x :=
    fun x y => rfl
  have htot : (0:ℝ) < totalConductance c := by
    show 0 < ∑ x, vertexConductance c x
    exact Finset.sum_pos (fun x _ => hpos x) Finset.univ_nonempty
  -- stochasticity
  have hrow : ∀ x : V, ∑ y, networkWalk c x y = 1 := by
    intro x
    have h : ∑ y, networkWalk c x y = (∑ y, c x y) / vertexConductance c x := by
      simp only [hentry, div_eq_mul_inv, ← Finset.sum_mul]
    rw [h]
    exact div_self (hpos x).ne'
  have hstoch : IsStochastic (networkWalk c) := by
    refine ⟨fun x y => ?_, hrow⟩
    rw [hentry]
    exact div_nonneg (hc.1 x y) (hpos x).le
  -- detailed balance
  have hdb : DetailedBalance (networkWalk c)
      (fun x => vertexConductance c x / totalConductance c) := by
    intro x y
    show vertexConductance c x / totalConductance c * networkWalk c x y
        = vertexConductance c y / totalConductance c * networkWalk c y x
    rw [hentry, hentry]
    have hx : vertexConductance c x ≠ 0 := (hpos x).ne'
    have hy : vertexConductance c y ≠ 0 := (hpos y).ne'
    have hcxy : c x y = c y x := hc.2 x y
    field_simp
    rw [hcxy]
  -- π is a distribution, and stationary
  have hdist : IsDist (fun x => vertexConductance c x / totalConductance c) := by
    refine ⟨fun x => div_nonneg (hpos x).le htot.le, ?_⟩
    show ∑ x, vertexConductance c x / totalConductance c = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    show (totalConductance c) * (totalConductance c)⁻¹ = 1
    exact mul_inv_cancel₀ htot.ne'
  refine ⟨hstoch, hdb, hdist, ?_⟩
  funext y
  show ∑ x, vertexConductance c x / totalConductance c * networkWalk c x y
      = vertexConductance c y / totalConductance c
  rw [Finset.sum_congr rfl fun x _ => (hdb y x).symm, ← Finset.mul_sum, hrow y, mul_one]
