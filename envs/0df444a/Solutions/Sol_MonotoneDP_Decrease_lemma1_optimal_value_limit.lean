-- Prove2me | solution 1 for MonotoneDP.Decrease.lemma1_optimal_value_limit
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:30:04.461787+00:00
-- url     : https://prove2.me/submissions/08c2f5b0-c656-4e8e-83e2-d37e087ba6e2

import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic
open MonotoneDP.Decrease Filter Topology
namespace CDecrease

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_antitone {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (π : m.Policy) :
    Antitone (fun N => m.comp π N m.Jbar) := by
  apply antitone_nat_of_succ_le
  intro N
  exact comp_mono m π N (fun x => hD x _ ((π N).2 x))

theorem Jpi_eq_iInf {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    m.Jpi π x=⨅ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iInf (fun i j hij => comp_antitone m hD π hij x)

theorem JN_antitone {S C : Type*} (m : Model S C) (hD : m.AssumptionD) : Antitone m.JN := by
  intro N K hNK x
  apply iInf_mono
  intro π
  exact comp_antitone m hD π hNK x
end CDecrease

theorem solution {S C : Type*} (m : Model S C) (hD : m.AssumptionD) :
    ∀ x, Tendsto (fun N => m.JN N x) atTop (𝓝 (m.Jstar x)) := by
  intro x
  have heq : m.Jstar x=⨅ N, m.JN N x := by
    simp only [Model.Jstar,CDecrease.Jpi_eq_iInf m hD,Model.JN]
    rw [iInf_comm]
  rw [heq]
  exact tendsto_atTop_iInf (fun i j hij => CDecrease.JN_antitone m hD hij x)
