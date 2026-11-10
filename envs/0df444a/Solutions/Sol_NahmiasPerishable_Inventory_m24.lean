-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m24
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:21:28.697561+00:00
-- url     : https://prove2.me/submissions/5729d1f4-f260-44b1-bc43-9c051a29ce74

import Definitions.Def_NahmiasPerishable_Inventory_Decay

open MeasureTheory Set
open scoped ENNReal
open NahmiasPerishable.Inventory

private noncomputable def u01Law : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

private instance : IsProbabilityMeasure u01Law := by
  constructor
  dsimp [u01Law]
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

private noncomputable def u01Demand : Demand where
  law := u01Law
  prob := inferInstance
  nonneg := by
    dsimp [u01Law]
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ (fun d hd => hd.1)
  density := (Icc (0 : ℝ) 1).indicator 1
  measurable_density := measurable_one.indicator measurableSet_Icc
  law_density := (withDensity_indicator_one measurableSet_Icc).symm

private lemma two_exp_neg_one_lt_one : 2 * Real.exp (-1) < 1 := by
  have h1 : (2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : 0 < Real.exp (-1) := Real.exp_pos (-1)
  have h3 : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith

private noncomputable def f24 (d : ℝ) : ℝ := 2 * Real.exp (-1) - d

private lemma measurable_f24 : Measurable f24 := by
  unfold f24
  fun_prop

private noncomputable def nu24 : Measure ℝ := u01Demand.law.map f24

private instance : IsProbabilityMeasure nu24 :=
  Measure.isProbabilityMeasure_map measurable_f24.aemeasurable

private lemma nu24_Iic_one : nu24 (Iic 1) = 1 := by
  dsimp [nu24]
  rw [Measure.map_apply measurable_f24 measurableSet_Iic]
  change (volume.restrict (Icc (0 : ℝ) 1)) (f24 ⁻¹' Iic 1) = 1
  rw [Measure.restrict_apply (measurable_f24 measurableSet_Iic)]
  have hsub : Icc (0 : ℝ) 1 ⊆ f24 ⁻¹' Iic 1 := by
    intro d hd
    simp only [mem_preimage, mem_Iic, f24]
    have h2e := two_exp_neg_one_lt_one
    linarith [hd.1]
  rw [inter_eq_self_of_subset_right hsub, Real.volume_Icc]
  norm_num

private lemma emmonsInvariant_nu24 : emmonsInvariant u01Demand 1 2 1 nu24 := by
  refine ⟨inferInstance, ?_⟩
  let μ := nu24.prod u01Demand.law
  let A : Set (ℝ × ℝ) := Iic 1 ×ˢ univ
  have hAmeas : MeasurableSet A := measurableSet_Iic.prod MeasurableSet.univ
  have hμA : μ A = 1 := by
    dsimp [μ, A]
    rw [Measure.prod_prod, nu24_Iic_one, measure_univ, mul_one]
  have haeA : ∀ᵐ xd ∂μ, xd ∈ A := by
    rw [ae_iff]
    change μ Aᶜ = 0
    rw [prob_compl_eq_zero_iff hAmeas]
    exact hμA
  have hae_eq : (fun xd : ℝ × ℝ => emmonsTransfer 1 2 1 xd.1 xd.2) =ᵐ[μ] (f24 ∘ Prod.snd) := by
    filter_upwards [haeA] with xd hxd
    have hx1 : xd.1 ≤ 1 := hxd.1
    unfold emmonsTransfer pos f24
    rw [if_pos hx1]
    dsimp only
    have hp2 : max (2 : ℝ) 0 = 2 := by norm_num
    have hn2 : max (-2 : ℝ) 0 = 0 := by norm_num
    rw [hp2, hn2]
    dsimp only [Function.comp_apply]
    ring
  rw [Measure.map_congr hae_eq, ← Measure.map_map measurable_f24 measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul]
  rfl

private lemma nu24_Ioo_neg2_neg1 : nu24 (Ioo (-2 : ℝ) (-1)) = 0 := by
  dsimp [nu24]
  rw [Measure.map_apply measurable_f24 measurableSet_Ioo]
  change (volume.restrict (Icc (0 : ℝ) 1)) (f24 ⁻¹' Ioo (-2 : ℝ) (-1)) = 0
  rw [Measure.restrict_apply (measurable_f24 measurableSet_Ioo)]
  have hempty : f24 ⁻¹' Ioo (-2 : ℝ) (-1) ∩ Icc (0 : ℝ) 1 = ∅ := by
    ext d
    simp only [mem_inter_iff, mem_preimage, mem_Ioo, mem_Icc, mem_empty_iff_false, iff_false,
      not_and, f24]
    intro h1 _ h22
    have hexp : 0 < Real.exp (-1) := Real.exp_pos (-1)
    linarith [h1.2]
  rw [hempty, measure_empty]

private lemma nu24_Ioo_neg1_zero_pos : 0 < nu24 (Ioo (-1 : ℝ) 0) := by
  dsimp [nu24]
  rw [Measure.map_apply measurable_f24 measurableSet_Ioo]
  change 0 < (volume.restrict (Icc (0 : ℝ) 1)) (f24 ⁻¹' Ioo (-1 : ℝ) 0)
  rw [Measure.restrict_apply (measurable_f24 measurableSet_Ioo)]
  have hsub : Ioo (2 * Real.exp (-1)) 1 ⊆ f24 ⁻¹' Ioo (-1 : ℝ) 0 ∩ Icc (0 : ℝ) 1 := by
    intro d hd
    have hexp : 0 < Real.exp (-1) := Real.exp_pos (-1)
    refine ⟨⟨?_, ?_⟩, ⟨by linarith [hd.1], le_of_lt hd.2⟩⟩
    · simp only [f24]; linarith [hd.2]
    · simp only [f24]; linarith [hd.1]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  linarith [two_exp_neg_one_lt_one]

private lemma g_eq_mul_exp {g : ℝ → ℝ}
    (hg : ∀ x < Real.exp (-1), HasDerivAt g (g x) x)
    (x : ℝ) (hx1 : -2 < x) (hx2 : x < Real.exp (-1)) :
    g x = g (-2) * Real.exp (x + 2) := by
  let h : ℝ → ℝ := fun t => g t * Real.exp (-t)
  have hh_deriv : ∀ t < Real.exp (-1), HasDerivAt h 0 t := by
    intro t ht
    have hd1 := hg t ht
    have hd2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-t) * -1) t :=
      (hasDerivAt_neg t).exp
    have hmul := hd1.mul hd2
    have hzero : g t * Real.exp (-t) + g t * (Real.exp (-t) * -1) = 0 := by ring
    rw [← hzero]
    exact hmul
  have hcont : ContinuousOn h (Icc (-2) x) := by
    intro t ht
    exact (hh_deriv t (lt_of_le_of_lt ht.2 hx2)).continuousAt.continuousWithinAt
  have hdiff : ∀ t ∈ Ioo (-2) x, HasDerivAt h 0 t :=
    fun t ht => hh_deriv t (lt_trans ht.2 hx2)
  rcases exists_hasDerivAt_eq_slope h (fun _ => (0 : ℝ)) hx1 hcont hdiff with ⟨c, _, hc⟩
  have hsub : h x - h (-2) = 0 := (div_eq_zero_iff.mp hc.symm).resolve_right (by linarith)
  have heq : g x * Real.exp (-x) = g (-2) * Real.exp (-(-2)) := by
    dsimp [h] at hsub
    linarith
  have h2x : - -2 + x = x + 2 := by ring
  calc g x = (g x * Real.exp (-x)) * Real.exp x := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = g (-2) * Real.exp (-(-2)) * Real.exp x := by rw [heq]
    _ = g (-2) * Real.exp (x + 2) := by
        rw [mul_assoc, ← Real.exp_add, h2x]

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (D : Demand) (s S theta : ℝ) (hs : 0 ≤ s) (hS : s < S)
    (htheta : 0 < theta) (ν : Measure ℝ) (hν : emmonsInvariant D s S theta ν),
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Measurable g ∧
      ν = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∀ x, (S*Real.exp (-2*theta) < x ∧ x < S*Real.exp (-theta)) ∨
          x < s*Real.exp (-theta) → HasDerivAt g (g x) x) ∧
      (∀ x, s*Real.exp (-theta) < x → x < S*Real.exp (-2*theta) →
        HasDerivAt g (g x-Real.exp theta*g (x*Real.exp theta)) x)) := by
  intro h
  rcases h u01Demand 1 2 1 (by norm_num) (by norm_num) (by norm_num) nu24 emmonsInvariant_nu24
    with ⟨g, hgnonneg, _, hνg, hderiv1, _⟩
  have hg_ode : ∀ x < Real.exp (-1), HasDerivAt g (g x) x := by
    intro x hx
    exact hderiv1 x (Or.inr (by linarith))
  have hexp_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
  rcases eq_or_lt_of_le (hgnonneg (-2)) with hg0 | hgpos
  · have hzero_on : ∀ x ∈ Ioo (-1 : ℝ) 0, ENNReal.ofReal (g x) = 0 := by
      intro x hx
      have hgx := g_eq_mul_exp hg_ode x (by linarith [hx.1]) (by linarith [hx.2])
      rw [hgx, ← hg0, zero_mul, ENNReal.ofReal_zero]
    have hmeas0 : nu24 (Ioo (-1 : ℝ) 0) = 0 := by
      rw [hνg, withDensity_apply _ measurableSet_Ioo]
      exact setLIntegral_eq_zero measurableSet_Ioo hzero_on
    exact (ne_of_gt nu24_Ioo_neg1_zero_pos) hmeas0
  · have hge_on : ∀ x ∈ Ioo (-2 : ℝ) (-1), ENNReal.ofReal (g (-2)) ≤ ENNReal.ofReal (g x) := by
      intro x hx
      have hgx := g_eq_mul_exp hg_ode x hx.1 (by linarith [hx.2])
      rw [hgx]
      apply ENNReal.ofReal_le_ofReal
      have h1 : 1 ≤ Real.exp (x + 2) := Real.one_le_exp (by linarith [hx.1])
      nlinarith
    have hmeas_ge : ENNReal.ofReal (g (-2)) * volume (Ioo (-2 : ℝ) (-1)) ≤
        nu24 (Ioo (-2 : ℝ) (-1)) := by
      rw [hνg, withDensity_apply _ measurableSet_Ioo, ← setLIntegral_const]
      exact setLIntegral_mono' measurableSet_Ioo hge_on
    rw [Real.volume_Ioo, nu24_Ioo_neg2_neg1] at hmeas_ge
    have hvol : (-1 : ℝ) - -2 = 1 := by norm_num
    rw [hvol, ENNReal.ofReal_one, mul_one] at hmeas_ge
    have hpos : 0 < ENNReal.ofReal (g (-2)) := ENNReal.ofReal_pos.mpr hgpos
    exact not_lt_of_ge hmeas_ge hpos
