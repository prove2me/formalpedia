-- Prove2me | solution 1 for MDPFinance.BayesianModels.lemma_5_4_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:47:42.537812+00:00
-- url     : https://prove2.me/submissions/d1d59de0-691a-4184-9cf8-448b101e0f7b

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior

open MeasureTheory ProbabilityTheory

namespace MDP542Aux

theorem main {Θ Z : Type*} [MeasurableSpace Θ] [MeasurableSpace Z]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Z) [SigmaFinite ν]
    (q : Θ → Z → ℝ) (hq : Measurable (fun p : Θ × Z => q p.1 p.2))
    (hprob : ∀ θ, ∫⁻ z, ENNReal.ofReal (q θ z) ∂ν = 1)
    (F : Z → ENNReal) (hF : Measurable F) (hFt : ∀ z, F z ≠ ⊤)
    (C : Set Θ)
    (hrec : ∀ z, 0 < (∫⁻ θ, ENNReal.ofReal (q θ z) ∂μ) →
      (∫⁻ θ, ENNReal.ofReal (q θ z) ∂μ) < ⊤ →
      F z = (∫⁻ θ in C, ENNReal.ofReal (q θ z) ∂μ) / (∫⁻ θ, ENNReal.ofReal (q θ z) ∂μ)) :
    ∫ z, (F z).toReal ∂(μ.bind fun θ => ν.withDensity fun z => ENNReal.ofReal (q θ z)) =
      (μ C).toReal := by
  have hq' : Measurable (Function.uncurry fun θ z => ENNReal.ofReal (q θ z)) := hq.ennreal_ofReal
  have hκ : Measurable (fun θ => ν.withDensity fun z => ENNReal.ofReal (q θ z)) := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp_rw [withDensity_apply _ hs]
    exact hq'.lintegral_prod_right'
  rw [integral_toReal hF.aemeasurable (Filter.Eventually.of_forall fun z => (hFt z).lt_top)]
  congr 1
  set m : Z → ENNReal := fun z => ∫⁻ θ, ENNReal.ofReal (q θ z) ∂μ with hm
  have hmint : ∫⁻ z, m z ∂ν = 1 := by
    simp only [hm]
    rw [← lintegral_lintegral_swap hq'.aemeasurable]
    simp [hprob]
  have hmfin : ∀ᵐ z ∂ν, m z < ⊤ := by
    have hmm : Measurable m := hq'.lintegral_prod_left'
    exact ae_lt_top hmm (by rw [hmint]; exact ENNReal.one_ne_top)
  rw [Measure.lintegral_bind hκ.aemeasurable hF.aemeasurable]
  simp_rw [lintegral_withDensity_eq_lintegral_mul _ (hq'.of_uncurry_left) hF]
  have hswap : ∫⁻ θ, ∫⁻ z, ((fun z => ENNReal.ofReal (q θ z)) * F) z ∂ν ∂μ =
      ∫⁻ z, ∫⁻ θ, ENNReal.ofReal (q θ z) * F z ∂μ ∂ν := by
    simp only [Pi.mul_apply]
    exact lintegral_lintegral_swap (hq'.mul (hF.comp measurable_snd)).aemeasurable
  rw [hswap]
  have step : ∀ᵐ z ∂ν, ∫⁻ θ, ENNReal.ofReal (q θ z) * F z ∂μ =
      ∫⁻ θ in C, ENNReal.ofReal (q θ z) ∂μ := by
    filter_upwards [hmfin] with z hz
    rw [lintegral_mul_const' _ _ (hFt z)]
    rcases eq_or_ne (m z) 0 with h0 | h0
    · have : ∫⁻ θ in C, ENNReal.ofReal (q θ z) ∂μ = 0 := by
        apply le_antisymm _ zero_le
        calc _ ≤ m z := setLIntegral_le_lintegral _ _
          _ = 0 := h0
      rw [this]
      change m z * F z = 0
      rw [h0, zero_mul]
    · change m z * F z = _
      rw [hrec z (pos_iff_ne_zero.2 h0) hz, ENNReal.mul_div_cancel h0 hz.ne]
  rw [lintegral_congr_ae step, lintegral_lintegral_swap]
  · simp [hprob]
  · exact (hq'.comp measurable_swap).aemeasurable
end MDP542Aux

open MDPFinance.BayesianModels in
theorem solution {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] (M : BayesModel EX Θ A Z) (Pf : M.Posterior)
    (n : ℕ) (xs : ℕ → EX) (as : ℕ → A) (zs : ℕ → Z) (han : as n ∈ M.Dx (xs n)) (C : Set Θ)
    (hC : MeasurableSet C) :
    ∫ z, (Pf.mu (n + 1) xs as (Function.update zs (n + 1) z) C).toReal
        ∂((Pf.mu n xs as zs).bind fun θ => M.nu.withDensity fun z =>
          ENNReal.ofReal (M.qZ (xs n) θ (as n) z)) =
      (Pf.mu n xs as zs C).toReal := by
  have := Pf.hmu_prob n xs as zs
  have := M.hnu_sigmaFinite
  have hq : Measurable fun p : Θ × Z => M.qZ (xs n) p.1 (as n) p.2 :=
    M.hqZ_meas.comp (show Measurable fun p : Θ × Z => (xs n, p.1, as n, p.2) by fun_prop)
  have hF : Measurable fun z => Pf.mu (n + 1) xs as (Function.update zs (n + 1) z) C :=
    (Pf.hmu_meas (n + 1) C hC).comp
      (measurable_const.prodMk (measurable_const.prodMk (measurable_update zs)))
  refine MDP542Aux.main (Pf.mu n xs as zs) M.nu (fun θ z => M.qZ (xs n) θ (as n) z) hq
    (fun θ => M.hqZ_prob _ _ _) _ hF (fun z => ?_) C (fun z h0 ht => ?_)
  · have := Pf.hmu_prob (n + 1) xs as (Function.update zs (n + 1) z)
    exact measure_ne_top _ _
  · have hdep : Pf.mu n xs as (Function.update zs (n + 1) z) = Pf.mu n xs as zs :=
      Pf.hmu_dep n xs xs as as _ _ (fun _ _ => rfl) (fun _ _ => rfl)
        (fun i _ hi => by rw [Function.update_of_ne (by omega)])
    have := Pf.hmu_rec n xs as (Function.update zs (n + 1) z)
    simp only [Function.update_self, hdep] at this
    exact this h0 ht C hC
