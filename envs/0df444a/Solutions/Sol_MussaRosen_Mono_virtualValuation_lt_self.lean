-- Prove2me | solution 1 for MussaRosen.Mono.virtualValuation_lt_self
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:25:28.616465+00:00
-- url     : https://prove2.me/submissions/13d7ad3e-fac2-4dd2-be3b-00ccc75be7ce

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology


namespace MussaRosen.Mono

theorem vv_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) :
    (∀ θ ∈ Set.Ico θlo θhi, virtualValuation D θ < θ) ∧ virtualValuation D θhi = θhi := by
  have hF1 : D.F θhi = 1 := by
    rw [D.F_eq θhi ⟨D.lo_lt_hi.le, le_rfl⟩]; exact D.f_total
  constructor
  · intro θ hθ
    have hθ' : θ ∈ Set.Icc θlo θhi := ⟨hθ.1, hθ.2.le⟩
    have hfθ := D.f_pos θ hθ'
    have h1 : D.F θ < 1 := by
      rw [D.F_eq θ hθ']
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (D.f_integrable.mono_set (by
          rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le D.lo_lt_hi.le]
          exact Set.Icc_subset_Icc le_rfl hθ.2.le)) (D.f_integrable.mono_set (by
          rw [Set.uIcc_of_le hθ.2.le, Set.uIcc_of_le D.lo_lt_hi.le]
          exact Set.Icc_subset_Icc hθ.1 le_rfl))
      have hpos : 0 < ∫ x in θ..θhi, D.f x := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on
        · exact D.f_integrable.mono_set (by
            rw [Set.uIcc_of_le hθ.2.le, Set.uIcc_of_le D.lo_lt_hi.le]
            exact Set.Icc_subset_Icc hθ.1 le_rfl)
        · intro x hx; exact D.f_pos x ⟨hθ.1.trans hx.1.le, hx.2.le⟩
        · exact hθ.2
      rw [D.f_total] at hsplit
      linarith
    unfold virtualValuation
    have : 0 < (1 - D.F θ) / D.f θ := div_pos (by linarith) hfθ
    linarith
  · unfold virtualValuation; rw [hF1]; simp

end MussaRosen.Mono

open MussaRosen.Mono


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) :
    (∀ θ ∈ Set.Ico θlo θhi, virtualValuation D θ < θ) ∧ virtualValuation D θhi = θhi := by
  exact vv_core D
