-- Prove2me | solution 1 for MDPFinance.LPDuality.proposition_7_5_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:24:35.731292+00:00
-- url     : https://prove2.me/submissions/c0d2a0c6-d6c0-4f54-8333-8860e36b84ff

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Discretization

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

open MeasureTheory ProbabilityTheory Filter Topology MDPFinance.LPDuality in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb0 : 0 < αb)
    (IMc : Set (E → ℝ)) (G : GridApprox M IMc) (hbdd : ∃ K : ℝ, ∀ x, |b x - G.bG x| ≤ K)
    (hmtilde1 : mtilde b G.bG < 1) :
    alphaG M G.bG ≤ αb * ((αb + mtilde b G.bG) / (αb * (1 - mtilde b G.bG))) ∧
      Tendsto (fun mt : ℝ => (αb + mt) / (αb * (1 - mt))) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  have := M.isMarkovQ
  obtain ⟨K, hK⟩ := hbdd
  have hbddA : BddAbove (Set.range fun x => |b x - G.bG x|) :=
    ⟨K, by rintro _ ⟨x, rfl⟩; exact hK x⟩
  have hmt0 : 0 ≤ mtilde b G.bG := Real.iSup_nonneg (fun x => abs_nonneg _)
  have hmtle : ∀ x, |b x - G.bG x| ≤ mtilde b G.bG := fun x => le_ciSup hbddA x
  have hαne : αb ≠ 0 := hαb0.ne'
  set mt := mtilde b G.bG with hmt
  have h1mt : 0 < 1 - mt := by linarith
  have hkey : αb * ((αb + mt) / (αb * (1 - mt))) = (αb + mt) / (1 - mt) := by
    rw [mul_div_assoc', mul_div_mul_left _ _ hαne]
  refine ⟨?_, ?_⟩
  · rw [hkey]
    have hRpos : 0 ≤ (αb + mt) / (1 - mt) := div_nonneg (by linarith) h1mt.le
    unfold alphaG
    refine Real.iSup_le (fun xa => ?_) hRpos
    refine Real.iSup_le (fun hxa => ?_) hRpos
    have hbx : 1 ≤ G.bG xa.1 := G.hbG_ge1 xa.1
    have hint : ∫ y, G.bG y ∂(M.Q xa) ≤ αb * b xa.1 + mt := by
      have hle : ∫⁻ y, ENNReal.ofReal (G.bG y) ∂(M.Q xa) ≤
          ENNReal.ofReal (αb * b xa.1 + mt) := by
        calc ∫⁻ y, ENNReal.ofReal (G.bG y) ∂(M.Q xa)
            ≤ ∫⁻ y, (ENNReal.ofReal (b y) + ENNReal.ofReal mt) ∂(M.Q xa) := by
              refine lintegral_mono (fun y => ?_)
              rw [← ENNReal.ofReal_add (hb.hb_nonneg y) hmt0]
              apply ENNReal.ofReal_le_ofReal
              have h2 := abs_le.mp (hmtle y)
              linarith [h2.1]
          _ = ∫⁻ y, ENNReal.ofReal (b y) ∂(M.Q xa) + ENNReal.ofReal mt := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          _ ≤ ENNReal.ofReal (αb * b xa.1) + ENNReal.ofReal mt := by
              gcongr
              exact hb.hQ xa hxa
          _ = ENNReal.ofReal (αb * b xa.1 + mt) := by
              rw [ENNReal.ofReal_add (mul_nonneg hb.hαb (hb.hb_nonneg _)) hmt0]
      rw [integral_eq_lintegral_of_nonneg_ae]
      · exact ENNReal.toReal_le_of_le_ofReal
          (by nlinarith [hb.hαb, hb.hb_nonneg xa.1]) hle
      · exact Filter.Eventually.of_forall (fun y => by simp only [Pi.zero_apply]; linarith [G.hbG_ge1 y])
      · exact G.hbG_meas.aestronglyMeasurable
    have hbb : b xa.1 ≤ G.bG xa.1 + mt := by
      have h3 := abs_le.mp (hmtle xa.1)
      linarith [h3.2]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < G.bG xa.1), div_mul_eq_mul_div, le_div_iff₀ h1mt]
    have hA := mul_le_mul_of_nonneg_right hint h1mt.le
    have hB : 0 ≤ αb * (G.bG xa.1 + mt - b xa.1) * (1 - mt) :=
      mul_nonneg (mul_nonneg hb.hαb (by linarith)) h1mt.le
    have hC : 0 ≤ (αb + 1) * mt * (G.bG xa.1 - 1 + mt) :=
      mul_nonneg (mul_nonneg (by linarith) hmt0) (by linarith)
    nlinarith [hA, hB, hC]
  · have hc : ContinuousAt (fun t : ℝ => (αb + t) / (αb * (1 - t))) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simp [hαne]
    have h4 := hc.tendsto
    simp only [add_zero, sub_zero, mul_one, div_self hαne] at h4
    exact h4.mono_left nhdsWithin_le_nhds
