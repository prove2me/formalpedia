-- Prove2me | solution 1 for MartOT.Abs.theorem_2_6_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:00:24.072976+00:00
-- url     : https://prove2.me/submissions/a0147c7c-9c42-4e6f-9694-03096dbf982a

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_StochasticOrders_MultivariateVariability_convex_order_martingale_coupling_iff_v2

open MeasureTheory ProbabilityTheory

lemma s26_toENNReal (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]

lemma s26_integralE_of_integrable {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    MartOT.Var.integralE μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h2 : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-f x) := fun x => by
    rw [← EReal.coe_neg, s26_toENNReal]
  simp only [s26_toENNReal, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hp : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ :=
    (lintegral_ofReal_le_lintegral_enorm f).trans_lt hf.2 |>.ne
  have hn : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤ :=
    (lintegral_ofReal_le_lintegral_enorm (fun x => -f x)).trans_lt hf.neg.2 |>.ne
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal hp, EReal.coe_ennreal_toReal hn]

lemma s26_mass {μ ν : Measure ℝ} (hμν : MartOT.Var.ConvexLE μ ν) : μ Set.univ = ν Set.univ := by
  obtain ⟨⟨hμf, -⟩, ⟨hνf, -⟩, h⟩ := hμν
  have h1 := h (fun _ => 1) (convexOn_const _ convex_univ)
  have h2 := h (fun _ => -1) (convexOn_const _ convex_univ)
  rw [s26_integralE_of_integrable (integrable_const _),
    s26_integralE_of_integrable (integrable_const _)] at h1 h2
  simp only [integral_const, smul_eq_mul, mul_one, mul_neg] at h1 h2
  have h1' : μ.real Set.univ ≤ ν.real Set.univ := by exact_mod_cast h1
  have h2' : -μ.real Set.univ ≤ -ν.real Set.univ := by exact_mod_cast h2
  have : μ.real Set.univ = ν.real Set.univ := le_antisymm h1' (by linarith)
  rw [measureReal_def, measureReal_def] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this

theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π := by
  have hmass := s26_mass hμν
  obtain ⟨⟨hμf, hμi⟩, ⟨hνf, hνi⟩, hcx⟩ := hμν
  by_cases h0 : μ Set.univ = 0
  · have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp h0
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.mp (hmass ▸ h0)
    refine ⟨0, ⟨?_, ?_⟩, integrable_zero_measure, fun _ _ _ => by simp⟩
    · simp [hμ0]
    · simp [hν0]
  set m : ENNReal := μ Set.univ with hm
  have hmtop : m ≠ ⊤ := measure_ne_top _ _
  set c : ENNReal := m⁻¹ with hc
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr hmtop
  have hctop : c ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  have hmc : m * c = 1 := ENNReal.mul_inv_cancel h0 hmtop
  set μ' : Measure ℝ := c • μ with hμ'
  set ν' : Measure ℝ := c • ν with hν'
  haveI : IsProbabilityMeasure μ' := ⟨by
    simp only [hμ', Measure.smul_apply, smul_eq_mul]; rw [mul_comm]; exact hmc⟩
  haveI : IsProbabilityMeasure ν' := ⟨by
    simp only [hν', Measure.smul_apply, smul_eq_mul, ← hmass]; rw [mul_comm]; exact hmc⟩
  set X : ℝ → Fin 1 → ℝ := fun x _ => x with hX
  have hXm : Measurable X := measurable_pi_lambda _ (fun _ => measurable_id)
  have hXi : ∀ η : Measure ℝ, Integrable (fun x : ℝ => x) η → Integrable X η := by
    intro η hη
    exact Integrable.of_eval (fun _ => hη)
  have hco : StochasticOrders.MultivariateVariability.ConvexOrder μ' ν' X X := by
    intro φ hφ hi1 hi2
    have hψ : ConvexOn ℝ Set.univ (φ ∘ X) := by
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      have := hφ.2 (Set.mem_univ (X x)) (Set.mem_univ (X y)) ha hb hab
      have hXe : a • X x + b • X y = X (a • x + b • y) := by
        funext i; simp [hX]
      simpa [Function.comp_apply, hXe] using this
    have hle := hcx (φ ∘ X) hψ
    have hi1' : Integrable (φ ∘ X) μ := (integrable_smul_measure hc0 hctop).mp hi1
    have hi2' : Integrable (φ ∘ X) ν := (integrable_smul_measure hc0 hctop).mp hi2
    rw [s26_integralE_of_integrable hi1', s26_integralE_of_integrable hi2'] at hle
    have hle' : ∫ x, (φ ∘ X) x ∂μ ≤ ∫ x, (φ ∘ X) x ∂ν := by exact_mod_cast hle
    show ∫ x, (φ ∘ X) x ∂μ' ≤ ∫ x, (φ ∘ X) x ∂ν'
    rw [hμ', hν', integral_smul_measure, integral_smul_measure]
    exact smul_le_smul_of_nonneg_left hle' ENNReal.toReal_nonneg
  have hμ'i : Integrable (fun x : ℝ => x) μ' := hμi.smul_measure hctop
  have hν'i : Integrable (fun x : ℝ => x) ν' := hνi.smul_measure hctop
  obtain ⟨Ω, mΩ, ρ, _, Xh, Yh, hXh, hYh, hidX, hidY, hcond⟩ :=
    (StochasticOrders.MultivariateVariability.convex_order_martingale_coupling_iff_v2 μ' ν' X X
      hXm hXm (hXi _ hμ'i) (hXi _ hν'i)).mp hco
  set T : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0 with hT
  have hXhi : Integrable Xh ρ := hidX.integrable_iff.mpr (hXi _ hμ'i)
  have hYhi : Integrable Yh ρ := hidY.integrable_iff.mpr (hXi _ hν'i)
  have hX0i : Integrable (fun ω => Xh ω 0) ρ := T.integrable_comp hXhi
  have hY0i : Integrable (fun ω => Yh ω 0) ρ := T.integrable_comp hYhi
  have hX0m : Measurable (fun ω => Xh ω 0) := measurable_pi_apply 0 |>.comp hXh
  have hY0m : Measurable (fun ω => Yh ω 0) := measurable_pi_apply 0 |>.comp hYh
  set F : Ω → ℝ × ℝ := fun ω => (Xh ω 0, Yh ω 0) with hF
  have hFm : Measurable F := hX0m.prodMk hY0m
  set π₀ : Measure (ℝ × ℝ) := ρ.map F with hπ₀
  -- marginal identities for π₀
  have hfst : π₀.map Prod.fst = μ' := by
    rw [hπ₀, Measure.map_map measurable_fst hFm]
    have : Prod.fst ∘ F = (fun v : Fin 1 → ℝ => v 0) ∘ Xh := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply 0) hXh, hidX.map_eq,
      Measure.map_map (measurable_pi_apply 0) hXm]
    exact Measure.map_id
  have hsnd : π₀.map Prod.snd = ν' := by
    rw [hπ₀, Measure.map_map measurable_snd hFm]
    have : Prod.snd ∘ F = (fun v : Fin 1 → ℝ => v 0) ∘ Yh := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply 0) hYh, hidY.map_eq,
      Measure.map_map (measurable_pi_apply 0) hXm]
    exact Measure.map_id
  -- martingale identity under ρ
  have hGle : MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ)) ≤ mΩ :=
    hXh.comap_le
  have hcond0 : ρ[fun ω => Yh ω 0 | MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ))] =ᵐ[ρ] fun ω => Xh ω 0 := by
    have h1 := T.comp_condExp_comm (m := MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ))) hYhi
    refine h1.symm.trans ?_
    filter_upwards [hcond] with ω hω
    simp [hT, Function.comp_apply, hω]
  have hmart : ∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      ∫ ω, f (Xh ω 0) * (Yh ω 0 - Xh ω 0) ∂ρ = 0 := by
    intro f hf ⟨C, hC⟩
    have hgm : StronglyMeasurable[MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ))] (fun ω => f (Xh ω 0)) := by
      have : Measurable[MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ))] Xh := comap_measurable Xh
      exact ((hf.comp (measurable_pi_apply 0)).comp this).stronglyMeasurable
    have hbd : ∀ᵐ ω ∂ρ, ‖f (Xh ω 0)‖ ≤ C :=
      Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hC _)
    have hgma : AEStronglyMeasurable (fun ω => f (Xh ω 0)) ρ :=
      (hf.comp hX0m).aestronglyMeasurable
    have iY : Integrable (fun ω => f (Xh ω 0) * Yh ω 0) ρ :=
      hY0i.bdd_mul hgma hbd
    have iX : Integrable (fun ω => f (Xh ω 0) * Xh ω 0) ρ := hX0i.bdd_mul hgma hbd
    have hpull := condExp_mul_of_stronglyMeasurable_left hgm iY hY0i
    have e1 : ∫ ω, f (Xh ω 0) * Yh ω 0 ∂ρ = ∫ ω, f (Xh ω 0) * Xh ω 0 ∂ρ := by
      calc ∫ ω, f (Xh ω 0) * Yh ω 0 ∂ρ
          = ∫ ω, (ρ[(fun ω => f (Xh ω 0)) * (fun ω => Yh ω 0) | MeasurableSpace.comap Xh (inferInstance : MeasurableSpace (Fin 1 → ℝ))]) ω ∂ρ :=
            (integral_condExp hGle (μ := ρ)
              (f := (fun ω => f (Xh ω 0)) * fun ω => Yh ω 0)).symm
        _ = ∫ ω, f (Xh ω 0) * Xh ω 0 ∂ρ := by
            apply integral_congr_ae
            filter_upwards [hpull, hcond0] with ω h1 h2
            rw [h1, Pi.mul_apply, h2]
    simp_rw [mul_sub]
    rw [integral_sub iY iX, e1, sub_self]
  -- the plan
  refine ⟨m • π₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Measure.map_smul, hfst, hμ', smul_smul, hmc, one_smul]
  · rw [Measure.map_smul, hsnd, hν', smul_smul, hmc, one_smul]
  · refine Integrable.smul_measure ?_ hmtop
    rw [hπ₀, integrable_map_measure (by fun_prop) hFm.aemeasurable]
    exact hY0i.sub hX0i
  · intro f hf hC
    rw [integral_smul_measure, hπ₀,
      integral_map hFm.aemeasurable (by
        exact ((hf.comp measurable_fst).mul (measurable_snd.sub measurable_fst)).aestronglyMeasurable)]
    simp only [hF]
    rw [hmart f hf hC, smul_zero]
