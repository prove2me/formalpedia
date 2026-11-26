-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45MinSquareEnergyV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:09.083742+00:00
-- url     : https://prove2.me/submissions/05c45f7a-a006-439d-846c-211cddb4eea8

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) :
    ∀ᵐ w ∂P, ∀ T : NNReal,
      Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2))
        ((N.N w).restrict (Ioc (0 : ℝ) (T : ℝ) ×ˢ Set.univ)) := by
  let g : ℝ → ℝ := fun x => min 1 (x^2)
  have hg : Measurable g := measurable_const.min (measurable_id.pow_const 2)
  have hn : ∀ x, 0 ≤ g x := fun x => le_min zero_le_one (sq_nonneg x)
  have hI : Integrable g ν := ⟨hg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).2 hν.2⟩
  have hM (n : ℕ) : ∀ᵐ w ∂P,
      Integrable (fun z : ℝ × ℝ => g z.2)
        ((N.N w).restrict (Ioc (0 : ℝ) ((n+1 : ℕ) : ℝ) ×ˢ Set.univ)) := by
    let R : Set (ℝ × ℝ) := Ioc (0 : ℝ) ((n+1 : ℕ) : ℝ) ×ˢ Set.univ
    have hR : MeasurableSet R := measurableSet_Ioc.prod MeasurableSet.univ
    let μ : Ω → Measure (ℝ × ℝ) := fun w => (N.N w).restrict R
    have hμ : Measurable μ := Measure.measurable_of_measurable_coe μ fun s hs => by
      simpa only [μ,Measure.restrict_apply hs] using N.measurable_eval (hs.inter hR)
    have hm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (g z.2)) :=
      ENNReal.measurable_ofReal.comp (hg.comp measurable_snd)
    have hfin := (Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1 P ν N g hg hn
      ((n+1 : ℕ) : NNReal) (by positivity)).2 hI
    have hmeas : Measurable (fun w => ∫⁻ z, ENNReal.ofReal (g z.2) ∂μ w) :=
      (Measure.measurable_lintegral hm).comp hμ
    have h := ae_lt_top hmeas (by simpa [μ,R] using hfin.ne)
    filter_upwards [h] with w hw
    exact ⟨(hg.comp measurable_snd).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z : ℝ × ℝ => hn z.2)).2 hw⟩
  filter_upwards [ae_all_iff.mpr hM] with w hw
  intro T
  obtain ⟨n,hnT⟩ := exists_nat_ge T
  apply (hw n).mono_measure
  exact Measure.restrict_mono (prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast hnT.trans (show (n : NNReal) ≤ ((n+1 : ℕ) : NNReal) by exact_mod_cast Nat.le_succ n))) subset_rfl) le_rfl
