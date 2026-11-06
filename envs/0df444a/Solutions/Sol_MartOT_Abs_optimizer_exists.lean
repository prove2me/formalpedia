-- Prove2me | solution 1 for MartOT.Abs.optimizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:58:16.812206+00:00
-- url     : https://prove2.me/submissions/1bd39923-d102-4ac1-993d-320a26c4d504

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_optimizer_exists

open MeasureTheory

/-- Scaling a plan by a finite constant scales its cost. -/
lemma hn73oe_cost_smul (c : ℝ → ℝ → ℝ) (ρ : Measure (ℝ × ℝ)) (r : ENNReal) (hr : r ≠ ⊤) :
    MartOT.Var.cost c (r • ρ) = (r : EReal) * MartOT.Var.cost c ρ := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  rw [lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, EReal.coe_ennreal_mul,
    EReal.coe_ennreal_mul, EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_ennreal_nonneg r)
      (fun h => hr (EReal.coe_ennreal_eq_top_iff.mp h))]

/-- Scaling a martingale plan by a finite constant. -/
lemma hn73oe_plan_smul {μ ν : Measure ℝ} {ρ : Measure (ℝ × ℝ)}
    (hρ : MartOT.Var.IsMartingalePlan μ ν ρ) (r : ENNReal) (hr : r ≠ ⊤) :
    MartOT.Var.IsMartingalePlan (r • μ) (r • ν) (r • ρ) := by
  obtain ⟨⟨h1, h2⟩, hi, hm⟩ := hρ
  refine ⟨⟨?_, ?_⟩, hi.smul_measure hr, fun f hf hb => ?_⟩
  · rw [Measure.map_smul, h1]
  · rw [Measure.map_smul, h2]
  · rw [integral_smul_measure, hm f hf hb, smul_zero]

theorem solution (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π, MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π, MartOT.Var.IsOptimal c μ ν π := by
  obtain ⟨π0, hπ0⟩ := hne
  haveI := hμ.1
  haveI := hν.1
  set m := μ Set.univ with hm
  have hmtop : m ≠ ⊤ := measure_ne_top μ _
  by_cases hm0 : m = 0
  · -- the zero problem: every plan vanishes
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp hm0
    have hzero : ∀ σ, MartOT.Var.IsMartingalePlan μ ν σ → σ = 0 := by
      intro σ hσ
      apply Measure.measure_univ_eq_zero.mp
      rw [← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
        hσ.1.1, hμ0, Measure.coe_zero, Pi.zero_apply]
    refine ⟨π0, hπ0, fun σ hσ => ?_⟩
    rw [hzero σ hσ, hzero π0 hπ0]
  · set k := m⁻¹ with hk
    have hktop : k ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0
    have hνuniv : ν Set.univ = m := by
      rw [hm, ← hπ0.1.1, ← hπ0.1.2, Measure.map_apply measurable_snd MeasurableSet.univ,
        Measure.map_apply measurable_fst MeasurableSet.univ]
      rfl
    haveI hμp : IsProbabilityMeasure (k • μ) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, ← hm, hk, ENNReal.inv_mul_cancel hm0 hmtop]⟩
    haveI hνp : IsProbabilityMeasure (k • ν) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, hνuniv, hk, ENNReal.inv_mul_cancel hm0 hmtop]⟩
    have hμ' : MartOT.Var.InM (k • μ) := ⟨inferInstance, hμ.2.smul_measure hktop⟩
    have hν' : MartOT.Var.InM (k • ν) := ⟨inferInstance, hν.2.smul_measure hktop⟩
    have hint' : MartOT.Var.SuffIntegrable (k • μ) (k • ν) c := by
      obtain ⟨a, b, ha, hb, hab⟩ := hint
      exact ⟨a, b, ha.smul_measure hktop, hb.smul_measure hktop, hab⟩
    obtain ⟨π', hπ'⟩ := MartOT.Opt.optimizer_exists (k • μ) (k • ν) hμ' hν' c hc hint'
      ⟨k • π0, hn73oe_plan_smul hπ0 k hktop⟩
    have hmk : m * k = 1 := ENNReal.mul_inv_cancel hm0 hmtop
    have hback : ∀ η : Measure ℝ, m • (k • η) = η := fun η => by
      rw [smul_smul, hmk, one_smul]
    refine ⟨m • π', ?_, fun σ hσ => ?_⟩
    · have := hn73oe_plan_smul hπ'.1 m hmtop
      rwa [hback, hback] at this
    · have h1 := hπ'.2 (k • σ) (hn73oe_plan_smul hσ k hktop)
      rw [hn73oe_cost_smul c π' m hmtop]
      calc (m : EReal) * MartOT.Var.cost c π'
          ≤ (m : EReal) * MartOT.Var.cost c (k • σ) :=
            mul_le_mul_of_nonneg_left h1 (EReal.coe_ennreal_nonneg m)
        _ = MartOT.Var.cost c σ := by
            rw [hn73oe_cost_smul c σ k hktop, ← mul_assoc, ← EReal.coe_ennreal_mul, hmk]
            simp
