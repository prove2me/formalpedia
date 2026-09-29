-- Prove2me | solution 1 for MonotoneDP.Decrease.cor6_2_stationary_bellman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:11:52.879553+00:00
-- url     : https://prove2.me/submissions/a17ba002-e8d4-4b57-9983-47081374c25b

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace MonotoneDP.Decrease

open Filter Topology

theorem aux_c62_comp_stat {S C : Type*} (m : Model S C) (μ : m.Selector) :
    ∀ (N : ℕ) (J : S → EReal), m.comp (m.stationary μ) N J = (m.Tmu μ)^[N] J
  | 0, _ => rfl
  | N + 1, J => by
    show m.comp (m.stationary μ) N (m.Tmu μ J) = _
    rw [aux_c62_comp_stat m μ N]
    rfl

theorem aux_c62_mono {S C : Type*} (m : Model S C) (μ : m.Selector) :
    Monotone (m.Tmu μ) :=
  fun J J' h x => m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_c62_anti {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (μ : m.Selector)
    (x : S) : Antitone (fun k : ℕ => (m.Tmu μ)^[k] m.Jbar x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hT : m.Tmu μ m.Jbar ≤ m.Jbar := fun y => hD y _ (μ.2 y)
  have := (aux_c62_mono m μ).iterate n hT
  simpa only [Function.iterate_succ_apply] using this x

theorem aux_c62_tend {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (μ : m.Selector)
    (x : S) : Tendsto (fun k : ℕ => (m.Tmu μ)^[k] m.Jbar x) atTop
      (𝓝 (⨅ k : ℕ, (m.Tmu μ)^[k] m.Jbar x)) :=
  tendsto_atTop_iInf (aux_c62_anti m hD μ x)

theorem aux_c62_Jmu {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (μ : m.Selector)
    (x : S) : m.Jmu μ x = ⨅ k : ℕ, (m.Tmu μ)^[k] m.Jbar x := by
  unfold Model.Jmu Model.Jpi
  simp only [aux_c62_comp_stat]
  exact (aux_c62_tend m hD μ x).limUnder_eq

end MonotoneDP.Decrease

open MonotoneDP.Decrease Filter Topology

theorem solution {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (μ : m.Selector) :
    m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.Tmu μ J' → J' ≤ m.Jmu μ := by
  constructor
  · funext x
    have key := hD1 (fun k => (m.Tmu μ)^[k] m.Jbar)
      (fun k => by
        intro y
        have := aux_c62_anti m hD μ y (Nat.zero_le k)
        simpa using this)
      (fun k y => aux_c62_anti m hD μ y (Nat.le_succ k))
      x (μ.1 x) (μ.2 x)
    have hlim : (fun y => limUnder atTop (fun k => (m.Tmu μ)^[k] m.Jbar y)) = m.Jmu μ := by
      funext y
      rw [aux_c62_Jmu m hD μ y]
      exact (aux_c62_tend m hD μ y).limUnder_eq
    rw [hlim] at key
    have hL : limUnder atTop (fun k => m.H x (μ.1 x) ((m.Tmu μ)^[k] m.Jbar)) = m.Jmu μ x := by
      have ht : Tendsto (fun k : ℕ => m.H x (μ.1 x) ((m.Tmu μ)^[k] m.Jbar)) atTop
          (𝓝 (⨅ k : ℕ, (m.Tmu μ)^[k] m.Jbar x)) := by
        have := (tendsto_add_atTop_iff_nat 1).mpr (aux_c62_tend m hD μ x)
        refine this.congr ?_
        intro k
        simp only [Function.iterate_succ_apply']
        rfl
      rw [ht.limUnder_eq, aux_c62_Jmu m hD μ x]
    rw [hL] at key
    exact key
  · intro J' hJ' hJT
    have h : ∀ k : ℕ, J' ≤ (m.Tmu μ)^[k] m.Jbar := by
      intro k
      induction k with
      | zero => exact hJ'
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hJT.trans (aux_c62_mono m μ ih)
    intro x
    rw [aux_c62_Jmu m hD μ x]
    exact le_iInf fun k => h k x
