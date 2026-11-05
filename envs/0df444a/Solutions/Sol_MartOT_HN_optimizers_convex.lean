-- Prove2me | solution 1 for MartOT.HN.optimizers_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:40:28.938339+00:00
-- url     : https://prove2.me/submissions/ba6b491a-a461-43ef-bbf8-a2a8aff19ba6

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

lemma hn73oc_cost_eq (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => -|y - x|) ρ =
      -((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((-|p.2 - p.1| : ℝ) : EReal).toENNReal = 0 := by
    intro p
    apply EReal.toENNReal_of_nonpos
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  have h2 : ∀ p : ℝ × ℝ, (-((-|p.2 - p.1| : ℝ) : EReal)).toENNReal =
      ENNReal.ofReal |p.2 - p.1| := fun p => by
    rw [← EReal.coe_neg, neg_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _),
      EReal.toReal_coe]
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]

lemma hn73oc_plan {μ ν : Measure ℝ} {π π' : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (hπ' : MartOT.Var.IsMartingalePlan μ ν π')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MartOT.Var.IsMartingalePlan μ ν (ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π') := by
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht.1 (by linarith [ht.2])]
    simp
  obtain ⟨⟨h1, h2⟩, hi, hm⟩ := hπ
  obtain ⟨⟨h1', h2'⟩, hi', hm'⟩ := hπ'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul, h1, h1',
      ← add_smul, hsum, one_smul]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul, h2, h2',
      ← add_smul, hsum, one_smul]
  · exact (hi.smul_measure ENNReal.ofReal_ne_top).add_measure
      (hi'.smul_measure ENNReal.ofReal_ne_top)
  · intro ρ hρ hC
    obtain ⟨C, hC⟩ := hC
    have hb : ∀ η : Measure (ℝ × ℝ), Integrable (fun p : ℝ × ℝ => p.2 - p.1) η →
        Integrable (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) η := by
      intro η hη
      refine hη.bdd_mul (c := C) (hρ.comp measurable_fst).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun p => by
        simpa [Real.norm_eq_abs] using hC p.1)
    rw [integral_add_measure ((hb π hi).smul_measure ENNReal.ofReal_ne_top)
      ((hb π' hi').smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, hm ρ hρ ⟨C, hC⟩, hm' ρ hρ ⟨C, hC⟩]
    simp

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : MartOT.Var.ConvexLE μ ν) (π π' : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π) (hπ' : MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν (ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π') := by
  refine ⟨hn73oc_plan hπ.1 hπ'.1 t ht, fun σ hσ => ?_⟩
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht.1 (by linarith [ht.2])]
    simp
  have e1 := hπ.2 π' hπ'.1
  have e2 := hπ'.2 π hπ.1
  rw [hn73oc_cost_eq, hn73oc_cost_eq, EReal.neg_le_neg_iff] at e1 e2
  have heq : (∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂π) = ∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂π' :=
    le_antisymm (EReal.coe_ennreal_le_coe_ennreal_iff.mp e2)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mp e1)
  have hcomb : MartOT.Var.cost (fun x y => -|y - x|)
      (ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π') =
      MartOT.Var.cost (fun x y => -|y - x|) π := by
    rw [hn73oc_cost_eq, hn73oc_cost_eq, lintegral_add_measure, lintegral_smul_measure,
      lintegral_smul_measure, ← heq, smul_eq_mul, smul_eq_mul, ← add_mul, hsum, one_mul]
  rw [hcomb]
  exact hπ.2 σ hσ
