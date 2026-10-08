-- Prove2me | solution 1 for KleywegtSAA.ExpRate.rateFn_pos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:32:36.229673+00:00
-- url     : https://prove2.me/submissions/dfc9b9e3-5728-4bee-bafb-056e4b5be94f

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology KleywegtSAA.ExpRate

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P) (hA : (0 : ℝ) ∈ interior (integrableExpSet Y P))
    (a : ℝ) (ha : ∫ ω, Y ω ∂P < a) :
    0 < rateFn P Y a := by
  have hd : HasDerivAt (fun t => t * a - cgf Y P t) (a - ∫ ω, Y ω ∂P) 0 := by
    have hc := (analyticAt_cgf hA).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero hA] at hc
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const a).sub hc using 1 <;> simp
  have hp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < slope (fun t => t * a - cgf Y P t) 0 t :=
    (hd.tendsto_slope.mono_left (nhdsWithin_mono _ (by
      intro x hx
      simpa using ne_of_gt hx))).eventually (eventually_gt_nhds (sub_pos.mpr ha))
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ integrableExpSet Y P :=
    Filter.mem_of_superset (nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hA)) (fun _ h => h)
  obtain ⟨t, ht, htP, htM⟩ := (eventually_mem_nhdsWithin.and (hp.and hm)).exists
  change 0 < t at ht
  have hpos : 0 < t * a - cgf Y P t := by
    have hh : 0 < t⁻¹ * (t * a - cgf Y P t) := by simpa [slope, cgf_zero] using htP
    exact (mul_pos_iff.mp hh).resolve_right (by intro h; linarith [inv_pos.mpr ht]) |>.2
  have hlog : BellWilliams2001.ThresholdPolicy.logMGF P Y t = (cgf Y P t : EReal) := by
    unfold BellWilliams2001.ThresholdPolicy.logMGF
    rw [← ofReal_integral_eq_lintegral_ofReal htM (Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
    exact ENNReal.log_ofReal_of_pos (mgf_pos htM)
  have hle : ((t * a : ℝ) : EReal) - BellWilliams2001.ThresholdPolicy.logMGF P Y t ≤ rateFn P Y a :=
    le_iSup_of_le t (le_iSup_of_le ht.le le_rfl)
  rw [hlog, ← EReal.coe_sub] at hle
  exact lt_of_lt_of_le (by exact_mod_cast hpos) hle

#print axioms solution
