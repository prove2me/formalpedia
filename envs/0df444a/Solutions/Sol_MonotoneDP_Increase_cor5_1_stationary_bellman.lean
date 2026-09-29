-- Prove2me | solution 1 for MonotoneDP.Increase.cor5_1_stationary_bellman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:53:00.806831+00:00
-- url     : https://prove2.me/submissions/1cd3fc1d-7ea5-476c-9e1b-dad631df8bf5

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace MonotoneDP.Increase

open Filter Topology

theorem aux_c51_comp_eq {S C : Type*} (m : Model S C) (μ : m.Selector) :
    ∀ (N : ℕ) (J : S → EReal), m.comp (m.stationary μ) N J = (m.Tmu μ)^[N] J := by
  intro N
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show m.comp (m.stationary μ) N (m.Tmu μ J) = _
    rw [ih, Function.iterate_succ_apply]

theorem aux_c51_mono {S C : Type*} (m : Model S C) (μ : m.Selector) :
    Monotone (m.Tmu μ) := by
  intro J J' h x
  exact m.mono x (μ.1 x) (μ.2 x) J J' h

theorem aux_c51_seq_mono {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (μ : m.Selector) :
    Monotone (fun n => (m.Tmu μ)^[n] m.Jbar) := by
  apply Monotone.monotone_iterate_of_le_map (aux_c51_mono m μ)
  intro x
  exact hI x (μ.1 x) (μ.2 x)

theorem aux_c51_Jmu_eq {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (μ : m.Selector)
    (x : S) : m.Jmu μ x = ⨆ n, (m.Tmu μ)^[n] m.Jbar x := by
  unfold Model.Jmu Model.Jpi
  simp only [aux_c51_comp_eq]
  apply Tendsto.limUnder_eq
  apply tendsto_atTop_iSup
  intro a b hab
  exact aux_c51_seq_mono m hI μ hab x

end MonotoneDP.Increase

open MonotoneDP.Increase
open Filter Topology

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ∀ μ : m.Selector, m.Jmu μ = m.Tmu μ (m.Jmu μ) ∧
      ∀ J' : S → EReal, m.Jbar ≤ J' → m.Tmu μ J' ≤ J' → m.Jmu μ ≤ J' := by
  intro μ
  have hseq := aux_c51_seq_mono m hI μ
  have hJ : ∀ x, m.Jmu μ x = ⨆ n, (m.Tmu μ)^[n] m.Jbar x := aux_c51_Jmu_eq m hI μ
  refine ⟨?_, ?_⟩
  · funext x
    have hge : ∀ k, m.Jbar ≤ (m.Tmu μ)^[k] m.Jbar := fun k => hseq (Nat.zero_le k)
    have h1 := hI1 (fun k => (m.Tmu μ)^[k] m.Jbar) hge (fun k => hseq (Nat.le_succ k))
      x (μ.1 x) (μ.2 x)
    have hlim : (fun y => limUnder atTop (fun k => (m.Tmu μ)^[k] m.Jbar y)) = m.Jmu μ := by
      funext y
      rw [hJ y]
      apply Tendsto.limUnder_eq
      apply tendsto_atTop_iSup
      intro a b hab
      exact hseq hab y
    rw [hlim] at h1
    show m.Jmu μ x = m.H x (μ.1 x) (m.Jmu μ)
    rw [← h1]
    have hshift : (fun k => m.H x (μ.1 x) ((m.Tmu μ)^[k] m.Jbar)) =
        fun k => (m.Tmu μ)^[k+1] m.Jbar x := by
      funext k
      rw [Function.iterate_succ_apply']
      rfl
    rw [hshift]
    symm
    apply Tendsto.limUnder_eq
    have ht : Tendsto (fun k => (m.Tmu μ)^[k] m.Jbar x) atTop (𝓝 (m.Jmu μ x)) := by
      rw [hJ x]
      apply tendsto_atTop_iSup
      intro a b hab
      exact hseq hab x
    exact ht.comp (tendsto_add_atTop_nat 1)
  · intro J' hJ' hT
    have hle : ∀ n, (m.Tmu μ)^[n] m.Jbar ≤ J' := by
      intro n
      induction n with
      | zero => exact hJ'
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans (aux_c51_mono m μ ih) hT
    intro x
    rw [hJ x]
    exact iSup_le fun n => hle n x
