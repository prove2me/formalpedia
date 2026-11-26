-- Prove2me | solution 1 for NisanRonen.Rounding.exists_polytime_solver_with_report_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:16:48.577122+00:00
-- url     : https://prove2.me/submissions/3edabc9d-5a04-4f0a-9fde-7eb2c43e2306
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_exact
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_polytime
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_respects_fixed_priority
import Theorems.Thm_NisanRonen_Rounding_allocation_certificates_with_spare_machine_or_trivial_instance
import Theorems.Thm_NisanRonen_Rounding_equal_counts_report_certificates
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_two_jobs_two_machines_report_certificates
import Theorems.Thm_NisanRonen_Rounding_reserved_capacity_report_certificates
import Theorems.Thm_NisanRonen_Rounding_allocation_certificates_of_no_overreport_on_comparator
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances

open NisanRonen.Rounding

set_option autoImplicit false

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, a < b → ∀ (n : ℕ) [NeZero n],
        ∃ f : List (Fin n → ℕ) → List (Fin n),
          Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
            (id : List (Fin n) → List (Fin n)) f) ∧
          IsExactRoundedSolver f δ a b ∧ CertificateCriterion f δ a b ε := by
  intro ε hε a ha
  obtain ⟨δ, hδ, hδa, hstep, hremaining⟩ :=
    boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances ε hε a ha
  refine ⟨δ, hδ, ?_⟩
  intro b hab n inst
  let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
  have hf : IsExactRoundedSolver f δ a b := boundedLoadDP_exact ha hδ n
  refine ⟨f, boundedLoadDP_polytime n _, hf, ?_⟩
  intro k t d ht hd hop y
  by_cases hsmall : n = 1 ∨ k ≤ 1 ∨ k < n
  · exact allocation_certificates_with_spare_machine_or_trivial_instance ha hδ hε.le
      hstep hsmall f hf t d ht hd hop y
  have hn : 2 ≤ n := by
    have := NeZero.pos n
    by_contra h
    exact hsmall (Or.inl (by omega))
  by_cases hcounts : k = n
  · subst k
    by_cases hn3 : 3 ≤ n
    · obtain ⟨rank, hinj, hpriority⟩ := boundedLoadDP_respects_fixed_priority (b := b) ha hδ n n
      exact equal_counts_report_certificates ha hab.le hδ hstep hn3 f hf rank hinj
        hpriority t d ht hd hop y
    · have hn2 : n = 2 := by omega
      subst n
      exact boundedLoadDP_two_jobs_two_machines_report_certificates ha hab.le hδ hδa hstep
        t d ht hd hop y
  have hkn : n < k := by
    by_contra h
    exact hsmall (Or.inr (Or.inr (by omega)))
  by_cases hover : ∃ j, roundUp δ (t (y j) j) < roundUp δ (d (y j) j)
  · by_cases hreserve : ∃ (M : ℝ) (c : ℕ), a ≤ M ∧ M ≤ b ∧ roundUp δ M = M ∧
        k - 1 ≤ (n - 2) * c ∧ (c : ℝ) * roundUp δ a < M ∧
        roundedMakespan δ y (corrStar y t) < M ∧
        M ≤ (1 + ε) * makespan y (corrStar y t)
    · obtain ⟨M, c, hMa, hMb, hgrid, hc, hspace, hy, hMt⟩ := hreserve
      have h := reserved_capacity_report_certificates ha hδ hMa hMb hgrid hn c hc hspace
        f hf t d ht hd hop y hy
      intro i hi
      obtain ⟨v, hv, hvi, hx, z, hz⟩ := h i hi
      exact ⟨v, hv, hvi, hx, z, hz.trans hMt⟩
    · exact hremaining b hab n hn k hkn t d ht hd hop y hover hreserve
  · apply allocation_certificates_of_no_overreport_on_comparator ha hδ
      (show δ ≤ ε * a by linarith) f t d (fun l j => (ht l j).1) hd y
    intro j
    exact le_of_not_gt (fun h => hover ⟨j, h⟩)
