-- Prove2me | solution 1 for MasulloRH.eventual_rational_theta_cutoff_trace_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:23:09.226485+00:00
-- url     : https://prove2.me/submissions/306afbfb-767e-46d0-ae93-3b7caf963c1b

-- New quantitative partial result for the open rational theta cutoff trace lower bound.
import Theorems.Thm_MasulloRH_off_line_reference_mass_le_seven_over_eighty_thousand
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Definitions.Def_MasulloRH_RationalThetaSpace
import Definitions.Def_MasulloRH_RegularizedTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH Filter
open scoped Topology

theorem solution (ε : ℝ) (hε : 7/80000 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
        |(cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re - (operatorTrace T).re| < ε := by
  classical
  let H := fun n : ℕ => rationalThetaAnnihilator ((n:ℝ)+1)
  let A := fun n : ℕ => H n →L[ℂ] H n
  let conv := fun (n : ℕ) (T : A n) =>
    IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T
  let err := fun (n : ℕ) (T : A n) =>
    (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re - (operatorTrace T).re
  have hex (n : ℕ) : ∃ T : A n, conv n T ∧
      ((∃ U : A n, conv n U ∧ ε ≤ |err n U|) → ε ≤ |err n T|) := by
    by_cases h : ∃ U : A n, conv n U ∧ ε ≤ |err n U|
    · obtain ⟨U,hU,hu⟩ := h
      exact ⟨U,hU,fun _ => hu⟩
    · have ht := (rational_theta_annihilator_jet_trace ((n:ℝ)+1) (by linarith [Nat.cast_nonneg (α:=ℝ) n])).2
        (regularizedTraceTest n 3) (regularized_test_admissible n 3)
      obtain ⟨T,hT⟩ := ht.exists
      exact ⟨T,hT.1,fun hh => (h hh).elim⟩
  choose T hT hbad using hex
  have h := rational_theta_cutoff_trace_defect T hT
  let D := ∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
    (zeroResolventTerm (1/2) 3 z.val).re
  have hlim : Tendsto (fun n => err n (T n)) atTop (𝓝 D) := h.1
  have hD : |D| < ε := by
    rw [abs_of_nonneg h.2.1]
    exact lt_of_le_of_lt off_line_reference_mass_le_seven_over_eighty_thousand hε
  filter_upwards [hlim.abs.eventually (gt_mem_nhds hD)] with n hn
  intro U hU
  apply lt_of_not_ge
  intro hle
  exact (not_le_of_gt hn) (hbad n ⟨U,hU,hle⟩)
