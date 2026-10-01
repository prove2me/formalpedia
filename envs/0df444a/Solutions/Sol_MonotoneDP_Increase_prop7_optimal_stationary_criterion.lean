-- Prove2me | solution 1 for MonotoneDP.Increase.prop7_optimal_stationary_criterion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:32:46.129867+00:00
-- url     : https://prove2.me/submissions/f8bcb553-bd54-4eb9-90a4-9e436dde819e

import Theorems.Thm_MonotoneDP_Increase_cor5_1_stationary_bellman
import Theorems.Thm_MonotoneDP_Increase_prop5_bellman_equation
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic
open MonotoneDP.Increase Filter Topology
namespace CIncrease

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  exact comp_mono m π N (fun x => hI x _ ((π N).2 x))

theorem Jpi_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x=⨆ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem policy_tendsto {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  rw [Jpi_eq_iSup m hI]
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem Jbar_le_Jstar {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  apply le_iInf
  intro π
  rw [Jpi_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem T_le_Tmu {S C : Type*} (m : Model S C) (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => iInf_le_of_le (μ.1 x) (iInf_le_of_le (μ.2 x) le_rfl)

theorem comp_head {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N+1) J=m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih => exact ih (m.Tmu (π (N+1)) J)

theorem Jpi_head {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (π : m.Policy) : m.Jpi π=m.Tmu (π 0) (m.Jpi (fun k => π (k+1))) := by
  funext x
  have h := hI1 (fun N => m.comp (fun k => π (k+1)) N m.Jbar)
    (fun N => comp_monotone m hI _ (Nat.zero_le N))
    (fun N => comp_monotone m hI _ (Nat.le_succ N)) x _ ((π 0).2 x)
  have hl : limUnder atTop (fun N => m.H x ((π 0).1 x) (m.comp (fun k => π (k+1)) N m.Jbar))=m.Jpi π x := by
    apply Tendsto.limUnder_eq
    change Tendsto (fun N => m.Tmu (π 0) (m.comp (fun k => π (k+1)) N m.Jbar) x) atTop (𝓝 (m.Jpi π x))
    simp_rw [← comp_head]
    exact (tendsto_add_atTop_iff_nat 1).mpr (policy_tendsto m hI π x)
  exact hl.symm.trans h
end CIncrease

theorem solution {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π=m.Jstar) → ∃ μ : m.Selector, m.Jmu μ=m.Jstar) := by
  have hb := (prop5_bellman_equation m hI hI1 hI2).1
  have hcriterion : ∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar := by
    intro μ
    have hμ := cor5_1_stationary_bellman m hI hI1 hI2 μ
    constructor
    · intro h
      rw [h] at hμ
      exact hμ.1.symm.trans hb
    · intro h
      apply le_antisymm
      · exact hμ.2 m.Jstar (CIncrease.Jbar_le_Jstar m hI) (by rw [h,← hb])
      · exact fun x => iInf_le (fun π : m.Policy => m.Jpi π x) (m.stationary μ)
  refine ⟨hcriterion,?_⟩
  rintro ⟨π,hπ⟩
  refine ⟨π 0,(hcriterion (π 0)).mpr ?_⟩
  apply le_antisymm
  · rw [← hb,← hπ]
    have hh := CIncrease.Jpi_head m hI hI1 π
    conv_rhs => rw [hh]
    intro x
    apply m.mono x _ ((π 0).2 x)
    intro y
    rw [hπ]
    exact iInf_le _ _
  · exact CIncrease.T_le_Tmu m (π 0) m.Jstar
