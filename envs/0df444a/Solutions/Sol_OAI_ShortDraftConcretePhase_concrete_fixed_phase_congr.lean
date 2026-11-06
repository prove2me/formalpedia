-- Prove2me | solution 1 for OAI.ShortDraftConcretePhase.concrete_fixed_phase_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:15.946347+00:00
-- url     : https://prove2.me/submissions/f33ff017-a2e1-4dbe-8b00-d3831226be7f

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ShortDraftCRT_addChar_congr_of_dvd
import Theorems.Thm_OAI_ShortDraftTrace_breveE_period_eisenstein


set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ShortDraftConcretePhase
open ShortDraftTrace
namespace OAI.ShortDraftConcretePhase
theorem _root_.solution (d a b x : eisensteinSubring)
    (hd : d ≠ 0) (hcong : d ∣ a - b) :
    breveE ((a : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) =
      breveE ((b : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) := by
  apply ShortDraftCRT.addChar_congr_of_dvd
    (Subring.subtype eisensteinSubring) breveE lamEis d a b x
  · have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    change (1 + 2 * ω₃ : ℂ) ≠ 0
    have hLam : 1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
      unfold ω₃
      ring
    rw [hLam]
    exact mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  · change (d : ℂ) ≠ 0
    intro h
    apply hd
    exact Subtype.ext h
  · exact breveE_period_eisenstein
  · exact hcong
end OAI.ShortDraftConcretePhase
