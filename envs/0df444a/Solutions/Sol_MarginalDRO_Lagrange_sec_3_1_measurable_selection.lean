-- Prove2me | solution 1 for MarginalDRO.Lagrange.sec_3_1_measurable_selection
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:22:40.715615+00:00
-- url     : https://prove2.me/submissions/ebac4e19-c4e9-42c5-9243-90000311d562

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

open MarginalDRO.Lagrange in
theorem solution {n : ℕ} (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ xstar : (Fin n → ℝ) → (Fin n → ℝ), Measurable xstar ∧
      ∀ c, xstar c ∈ 𝒳 ∧ ∀ x ∈ 𝒳, ∑ i, c i * x i ≤ ∑ i, c i * xstar c i := by
  classical
  suffices H : ∀ s : Finset (Fin n → ℝ), s.Nonempty → ∃ xs : (Fin n → ℝ) → (Fin n → ℝ),
      Measurable xs ∧ ∀ c, xs c ∈ s ∧ ∀ x ∈ s, ∑ i, c i * x i ≤ ∑ i, c i * xs c i from
    H 𝒳 h𝒳
  intro s
  refine Finset.induction_on s (fun h => absurd h Finset.not_nonempty_empty) ?_
  intro a s ha ih _
  rcases s.eq_empty_or_nonempty with hs | hs
  · subst hs
    refine ⟨fun _ => a, measurable_const, fun c => ⟨by simp, fun x hx => ?_⟩⟩
    simp only [insert_empty_eq, Finset.mem_singleton] at hx
    subst hx
    exact le_rfl
  · obtain ⟨f, hfm, hf⟩ := ih hs
    refine ⟨fun c => if ∑ i, c i * f c i ≤ ∑ i, c i * a i then a else f c, ?_, fun c => ?_⟩
    · have h1 : Measurable fun c : Fin n → ℝ => ∑ i, c i * f c i :=
        Finset.measurable_sum _ (fun i _ =>
          (measurable_pi_apply i).mul ((measurable_pi_apply i).comp hfm))
      have h2 : Measurable fun c : Fin n → ℝ => ∑ i, c i * a i :=
        Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).mul measurable_const)
      exact Measurable.ite (measurableSet_le h1 h2) measurable_const hfm
    · by_cases h : ∑ i, c i * f c i ≤ ∑ i, c i * a i
      · simp only [if_pos h]
        refine ⟨Finset.mem_insert_self _ _, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact le_rfl
        · exact le_trans ((hf c).2 x hx) h
      · simp only [if_neg h]
        refine ⟨Finset.mem_insert_of_mem (hf c).1, fun x hx => ?_⟩
        rcases Finset.mem_insert.1 hx with rfl | hx
        · push_neg at h; exact h.le
        · exact (hf c).2 x hx
