-- Prove2me | solution 1 for HeathcoteUnbounded.psi_not_mem_momentumDomain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:20:52.70785+00:00
-- url     : https://prove2.me/submissions/2799883c-5724-47c1-97c4-2fffee6300ff

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi
open MeasureTheory HeathcoteUnbounded Set

theorem solution :
    ¬ ∃ g : ℝ → ℂ, psi =ᵐ[volume] g ∧ ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b := by
  rintro ⟨g, hg, hac⟩
  have hc : ContinuousOn g (Icc 0 2) := by
    have := (hac 0 2).continuousOn
    rwa [uIcc_of_le (by norm_num)] at this
  have hcl : ∀ a b : ℝ, a < b → Icc a b ⊆ closure (interior (Icc a b)) := by
    intro a b hab; rw [interior_Icc, closure_Ioo hab.ne]
  -- left piece: g = 0 on [0,1]
  have hL : EqOn g (fun _ => (0:ℂ)) (Icc 0 1) := by
    refine Measure.eqOn_of_ae_eq (μ := (volume : Measure ℝ)) ?_ (hc.mono (Icc_subset_Icc le_rfl (by norm_num))) continuousOn_const
      (hcl 0 1 (by norm_num))
    have h1 : g =ᵐ[volume.restrict (Icc 0 1)] psi := (ae_restrict_of_ae hg.symm)
    refine h1.trans ?_
    have hIco : (Ico (0:ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc 0 1 : Set ℝ) := Ico_ae_eq_Icc
    rw [← Measure.restrict_congr_set hIco]
    refine (ae_restrict_mem measurableSet_Ico).mono (fun x hx => ?_)
    simp [psi, not_le.2 hx.2]
  have hR : EqOn g (fun x => ((x:ℂ))⁻¹) (Icc 1 2) := by
    refine Measure.eqOn_of_ae_eq (μ := (volume : Measure ℝ)) ?_ (hc.mono (Icc_subset_Icc (by norm_num) le_rfl)) ?_ (hcl 1 2 (by norm_num))
    · have h1 : g =ᵐ[volume.restrict (Icc 1 2)] psi := (ae_restrict_of_ae hg.symm)
      refine h1.trans ?_
      refine (ae_restrict_mem measurableSet_Icc).mono (fun x hx => ?_)
      simp [psi, hx.1]
    · apply ContinuousOn.inv₀ (Complex.continuous_ofReal.continuousOn)
      intro x hx; have : (1:ℝ) ≤ x := hx.1; exact_mod_cast (by linarith : x ≠ 0)
  have e1 := hL (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have e2 := hR (show (1:ℝ) ∈ Icc 1 2 by norm_num)
  simp at e1 e2
  rw [e1] at e2
  exact zero_ne_one e2
