-- Prove2me | solution 1 for MartOT.Abs.reduced_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:07:07.710188+00:00
-- url     : https://prove2.me/submissions/d7cb384a-002f-46fe-a536-12c565efde3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Abs_stay_part_eq_inf

open MeasureTheory

lemma ro_cost_eq (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => |y - x|) ρ =
      ((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((|p.2 - p.1| : ℝ) : EReal).toENNReal = ENNReal.ofReal |p.2 - p.1| :=
    fun p => by
      rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ p : ℝ × ℝ, (-((|p.2 - p.1| : ℝ) : EReal)).toENNReal = 0 := by
    intro p
    apply EReal.toENNReal_of_nonpos
    rw [← EReal.coe_neg]
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    MartOT.Var.IsOptimal (fun x y => |y - x|) (μ - μ ⊓ ν) (ν - μ ⊓ ν)
        (π - (μ ⊓ ν).map (fun x : ℝ => (x, x))) ∧
      (μ - μ ⊓ ν) ⊓ (ν - μ ⊓ ν) = 0 := by
  set c : ℝ → ℝ → ℝ := fun x y => |y - x| with hc
  set Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2} with hΔdef
  have hΔ : MeasurableSet Δ := measurableSet_eq_fun measurable_fst measurable_snd
  set m : Measure ℝ := μ ⊓ ν with hm
  have hmf : IsFiniteMeasure m := isFiniteMeasure_of_le μ inf_le_left
  have hdiag : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  set stay : Measure (ℝ × ℝ) := m.map (fun x : ℝ => (x, x)) with hstay
  have hsf : IsFiniteMeasure stay := by rw [hstay]; infer_instance
  have hstay_fst : stay.map Prod.fst = m := by
    rw [hstay, Measure.map_map measurable_fst hdiag]; exact Measure.map_id
  have hstay_snd : stay.map Prod.snd = m := by
    rw [hstay, Measure.map_map measurable_snd hdiag]; exact Measure.map_id
  have hstay_int : ∀ f : ℝ × ℝ → ℝ, Measurable f → (∀ x, f (x, x) = 0) → ∫ p, f p ∂stay = 0 := by
    intro f hf h0
    rw [hstay, integral_map hdiag.aemeasurable hf.aestronglyMeasurable]
    simp [h0]
  have hstay_lint : ∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂stay = 0 := by
    rw [hstay, lintegral_map (by fun_prop) hdiag]
    simp
  have hstay_integrable : Integrable (fun p : ℝ × ℝ => p.2 - p.1) stay := by
    rw [hstay, integrable_map_measure (by fun_prop) hdiag.aemeasurable]
    simp [Function.comp_def]
  -- decomposition of `π`
  have h1 := MartOT.Abs.stay_part_eq_inf μ ν hμν π hπ
  set σ0 : Measure (ℝ × ℝ) := π.restrict Δᶜ with hσ0
  have hsplit : π = stay + σ0 := by
    calc π = π.restrict Δ + π.restrict Δᶜ := (Measure.restrict_add_restrict_compl hΔ).symm
      _ = stay + σ0 := by rw [h1]
  have hsub : π - stay = σ0 := by
    rw [hsplit, add_comm]; exact Measure.add_sub_cancel
  obtain ⟨⟨⟨hp1, hp2⟩, hpi, hpm⟩, hopt⟩ := hπ
  have hσ0_fst : σ0.map Prod.fst = μ - m := by
    have : μ = m + σ0.map Prod.fst := by
      rw [← hp1, hsplit, Measure.map_add _ _ measurable_fst, hstay_fst]
    rw [this, add_comm]; exact Measure.add_sub_cancel.symm
  have hσ0_snd : σ0.map Prod.snd = ν - m := by
    have : ν = m + σ0.map Prod.snd := by
      rw [← hp2, hsplit, Measure.map_add _ _ measurable_snd, hstay_snd]
    rw [this, add_comm]; exact Measure.add_sub_cancel.symm
  have hbdd : ∀ (ρ : ℝ → ℝ), Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∀ η : Measure (ℝ × ℝ), Integrable (fun p : ℝ × ℝ => p.2 - p.1) η →
      Integrable (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) η := by
    intro ρ hρ ⟨C, hC⟩ η hη
    refine hη.bdd_mul (c := C) (hρ.comp measurable_fst).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hC p.1)
  have hσ0i : Integrable (fun p : ℝ × ℝ => p.2 - p.1) σ0 := hpi.restrict
  have hσ0plan : MartOT.Var.IsMartingalePlan (μ - m) (ν - m) σ0 := by
    refine ⟨⟨hσ0_fst, hσ0_snd⟩, hσ0i, fun ρ hρ hC => ?_⟩
    have hmart := hpm ρ hρ hC
    rw [hsplit, integral_add_measure (hbdd ρ hρ hC _ hstay_integrable) (hbdd ρ hρ hC _ hσ0i),
      hstay_int (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1))
        ((hρ.comp measurable_fst).mul (measurable_snd.sub measurable_fst))
        (fun x => by simp), zero_add] at hmart
    exact hmart
  refine ⟨⟨?_, fun σ hσ => ?_⟩, ?_⟩
  · rw [hsub]; exact hσ0plan
  · -- optimality in the reduced problem
    obtain ⟨⟨hs1, hs2⟩, hsi, hsm⟩ := hσ
    have hplan : MartOT.Var.IsMartingalePlan μ ν (stay + σ) := by
      refine ⟨⟨?_, ?_⟩, hstay_integrable.add_measure hsi, fun ρ hρ hC => ?_⟩
      · rw [Measure.map_add _ _ measurable_fst, hstay_fst, hs1, add_comm]
        exact Measure.sub_add_cancel_of_le inf_le_left
      · rw [Measure.map_add _ _ measurable_snd, hstay_snd, hs2, add_comm]
        exact Measure.sub_add_cancel_of_le inf_le_right
      · rw [integral_add_measure (hbdd ρ hρ hC _ hstay_integrable) (hbdd ρ hρ hC _ hsi),
          hstay_int (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1))
        ((hρ.comp measurable_fst).mul (measurable_snd.sub measurable_fst))
            (fun x => by simp), zero_add]
        exact hsm ρ hρ hC
    have hle := hopt _ hplan
    rw [hsub]
    rw [ro_cost_eq, ro_cost_eq, lintegral_add_measure, hstay_lint, zero_add] at hle
    rw [hsplit, lintegral_add_measure, hstay_lint, zero_add] at hle
    rw [ro_cost_eq, ro_cost_eq]
    exact hle
  · -- the reduced marginals are mutually singular in the lattice sense
    set κ := (μ - m) ⊓ (ν - m) with hκ
    have hκμ : κ + m ≤ μ := by
      calc κ + m ≤ (μ - m) + m := by gcongr; exact inf_le_left
        _ = μ := Measure.sub_add_cancel_of_le inf_le_left
    have hκν : κ + m ≤ ν := by
      calc κ + m ≤ (ν - m) + m := by gcongr; exact inf_le_right
        _ = ν := Measure.sub_add_cancel_of_le inf_le_right
    have hκm : κ + m ≤ m := le_inf hκμ hκν
    ext s hs
    have h := hκm s
    rw [Measure.add_apply] at h
    have hfin : m s ≠ ⊤ := measure_ne_top m s
    have : κ s = 0 := by
      have h' : κ s + m s ≤ 0 + m s := by rwa [zero_add]
      exact le_antisymm ((ENNReal.add_le_add_iff_right hfin).mp h') (zero_le)
    simpa using this
