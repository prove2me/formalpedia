-- Prove2me | solution 1 for OAI.CriticalZ3.zero_one_of_finite_alteration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:37:47.621297+00:00
-- url     : https://prove2.me/submissions/91811800-0146-47f1-a2fb-2117da5617ec

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution {E : Type uE} (μ : Measure (E → Bool))
    (hi : iIndepFun (fun e (ω : E → Bool) => ω e) μ)
    (A : Set (E → Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (J : Finset E) (ω ω' : E → Bool),
      (∀ e ∉ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : μ A = 0 ∨ μ A = 1 := by
  classical
  set s : E → MeasurableSpace (E → Bool) := fun e => MeasurableSpace.comap (fun ω : E → Bool => ω e) inferInstance with hs
  have h_le : ∀ e, s e ≤ (inferInstance : MeasurableSpace (E → Bool)) := fun e =>
    (measurable_pi_apply e).comap_le
  have h_indep : iIndep s μ := (iIndepFun_iff_iIndep (fun _ => inferInstance) _ μ).mp hi
  have htail : MeasurableSet[Filter.limsup s Filter.cofinite] A := by
    rw [Filter.limsup_eq_iInf_iSup]
    simp only [MeasurableSpace.measurableSet_iInf]
    intro S hS
    rw [Filter.mem_cofinite] at hS
    let π : (E → Bool) → (E → Bool) := fun ω e => if e ∈ S then ω e else false
    have hπ : @Measurable _ _ (⨆ a ∈ S, s a) MeasurableSpace.pi π := by
      refine @measurable_pi_iff _ _ _ (⨆ a ∈ S, s a) _ _ |>.mpr ?_
      intro e
      by_cases he : e ∈ S
      · simp only [π, he, if_true]
        have : s e ≤ ⨆ a ∈ S, s a := le_iSup₂ (f := fun a (_ : a ∈ S) => s a) e he
        exact Measurable.mono (comap_measurable (fun ω : E → Bool => ω e)) this le_rfl
      · simp only [π, he, if_false]
        exact measurable_const
    have hA' : π ⁻¹' A = A := by
      ext ω
      exact hinv hS.toFinset ω (π ω) (fun e he => by
        simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not] at he
        simp [π, he])
    rw [← hA']
    exact hπ hA
  exact measure_zero_or_one_of_measurableSet_limsup h_le h_indep
    (p := Set.Finite) (f := Filter.cofinite) (fun t ht => by simpa [Filter.mem_cofinite] using ht)
    (ns := fun J : Finset E => (J : Set E))
    (fun J K => ⟨J ∪ K, by simp, by simp⟩) (fun J => J.finite_toSet)
    (fun e => ⟨{e}, by simp⟩) htail

