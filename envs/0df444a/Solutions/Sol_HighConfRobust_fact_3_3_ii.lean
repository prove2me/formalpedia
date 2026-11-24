-- Prove2me | solution 1 for HighConfRobust.fact_3_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:56:29.507807+00:00
-- url     : https://prove2.me/submissions/9c7992df-8fd9-4440-8a4d-00b0b32d5143

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

open MeasureTheory ProbabilityTheory HighConfRobust

namespace Fact33ii

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma rd_of_ne_one {q : ℝ} (hq : q ≠ 1) (μ ν : Measure α) :
    renyiDivergence q μ ν = PADMPriv.renyiDiv q μ ν := by
  simp only [renyiDivergence, if_neg hq]

lemma rd_one (μ ν : Measure α) :
    renyiDivergence 1 μ ν = ((InformationTheory.klDiv μ ν : ENNReal) : EReal) := by
  rw [renyiDivergence, if_pos rfl]

/-- The power integral is nonzero for a probability measure absolutely continuous wrt `ν`. -/
lemma integral_pow_ne_zero {q : ℝ} (hq : 0 < q) (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] (hac : μ ≪ ν) :
    ∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν ≠ 0 := by
  intro h0
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  have h1 : μ.rnDeriv ν =ᵐ[ν] 0 := by
    filter_upwards [h0] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rcases (ENNReal.rpow_eq_zero_iff).mp hx with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · linarith
  have : μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  have hu : μ Set.univ = 0 := by
    rw [this, withDensity_congr_ae h1, withDensity_zero]; rfl
  simp at hu

lemma rd_ne_bot {q : ℝ} (hq : 1 ≤ q) (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] : renyiDivergence q μ ν ≠ ⊥ := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h; rw [rd_one]; exact EReal.coe_ennreal_ne_bot _
  · rw [rd_of_ne_one h.ne']
    unfold PADMPriv.renyiDiv
    split_ifs with hac
    · have hI := integral_pow_ne_zero (by linarith) μ ν hac
      have hlog : ENNReal.log (∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν) ≠ ⊥ := by
        simpa [ENNReal.log_eq_bot_iff] using hI
      have hc : (0 : ℝ) < (q - 1)⁻¹ := inv_pos.mpr (by linarith)
      induction h' : ENNReal.log (∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν) with
      | bot => exact absurd h' hlog
      | top => rw [EReal.mul_top_of_pos (by exact_mod_cast hc)]; simp
      | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    · simp

lemma rd_self {q : ℝ} (hq : 1 ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] :
    renyiDivergence q μ μ = 0 := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h; rw [rd_one, InformationTheory.klDiv_self]; simp
  · rw [rd_of_ne_one h.ne']
    unfold PADMPriv.renyiDiv
    rw [if_pos Measure.AbsolutelyContinuous.rfl]
    have : ∫⁻ x, (μ.rnDeriv μ x) ^ q ∂μ = 1 := by
      rw [lintegral_congr_ae (g := fun _ => 1)]
      · simp
      · filter_upwards [Measure.rnDeriv_self μ] with x hx
        rw [hx]; simp
    rw [this]; simp

lemma rd_map_equiv {q : ℝ} (hq : 1 ≤ q) (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    renyiDivergence q (μ.map e) (ν.map e) = renyiDivergence q μ ν := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [rd_one, rd_one]
    congr 1
    apply le_antisymm (InformationTheory.klDiv_map_le μ ν e.measurable)
    have := InformationTheory.klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
    simpa using this
  · rw [rd_of_ne_one h.ne', rd_of_ne_one h.ne']
    unfold PADMPriv.renyiDiv
    have hiff : μ.map e ≪ ν.map e ↔ μ ≪ ν := by
      constructor
      · intro hac
        have := hac.map e.symm.measurable
        simpa using this
      · intro hac; exact hac.map e.measurable
    by_cases hac : μ ≪ ν
    · rw [if_pos (hiff.mpr hac), if_pos hac]
      congr 3
      rw [lintegral_map_equiv]
      apply lintegral_congr_ae
      filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
      rw [hx]
    · rw [if_neg (fun h' => hac (hiff.mp h')), if_neg hac]

lemma rd_prod {q : ℝ} (hq : 1 ≤ q) (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₂] :
    renyiDivergence q (μ₁.prod μ₂) (ν₁.prod ν₂) =
      renyiDivergence q μ₁ ν₁ + renyiDivergence q μ₂ ν₂ := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [rd_one, rd_one, rd_one, ← EReal.coe_ennreal_add]
    congr 1
    rw [← Measure.compProd_const, ← Measure.compProd_const,
      InformationTheory.klDiv_compProd_eq_add, Measure.compProd_const, Measure.compProd_const]
    congr 1
    have h1 := rd_map_equiv (q := 1) le_rfl MeasurableEquiv.prodComm (μ₁.prod μ₂) (μ₁.prod ν₂)
    rw [rd_one, rd_one] at h1
    have e1 : (μ₁.prod μ₂).map MeasurableEquiv.prodComm = μ₂.prod μ₁ := Measure.prod_swap
    have e2 : (μ₁.prod ν₂).map MeasurableEquiv.prodComm = ν₂.prod μ₁ := Measure.prod_swap
    rw [e1, e2] at h1
    have h1' := EReal.coe_ennreal_injective h1
    rw [← h1', ← Measure.compProd_const, ← Measure.compProd_const,
      InformationTheory.klDiv_compProd_left]
  · have hq0 : 0 ≤ q := by linarith
    rw [rd_of_ne_one h.ne', rd_of_ne_one h.ne', rd_of_ne_one h.ne']
    unfold PADMPriv.renyiDiv
    by_cases h1 : μ₁ ≪ ν₁
    · by_cases h2 : μ₂ ≪ ν₂
      · have hprod : μ₁.prod μ₂ = (ν₁.prod ν₂).withDensity
            (fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) := by
          conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h1,
            ← Measure.withDensity_rnDeriv_eq _ _ h2]
          exact prod_withDensity (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _)
        have hac : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := by
          rw [hprod]; exact withDensity_absolutelyContinuous _ _
        rw [if_pos hac, if_pos h1, if_pos h2]
        have hI : ∫⁻ z, ((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z) ^ q ∂(ν₁.prod ν₂) =
            (∫⁻ x, (μ₁.rnDeriv ν₁ x) ^ q ∂ν₁) * ∫⁻ y, (μ₂.rnDeriv ν₂ y) ^ q ∂ν₂ := by
          rw [← lintegral_prod_mul (by fun_prop) (by fun_prop)]
          apply lintegral_congr_ae
          have hd := Measure.rnDeriv_withDensity (ν₁.prod ν₂)
            (f := fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) (by fun_prop)
          rw [← hprod] at hd
          filter_upwards [hd] with z hz
          rw [hz, ENNReal.mul_rpow_of_nonneg _ _ hq0]
        rw [hI, ENNReal.log_mul_add]
        exact EReal.left_distrib_of_nonneg_of_ne_top
          (by exact_mod_cast (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ q - 1)))
          (EReal.coe_ne_top _) _ _
      · have hnac : ¬ μ₁.prod μ₂ ≪ ν₁.prod ν₂ := by
          intro hac
          apply h2
          refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
          have := hac (s := Set.univ ×ˢ s) (by rw [Measure.prod_prod, h0, mul_zero])
          rw [Measure.prod_prod] at this
          simpa using this
        rw [if_neg hnac, if_neg h2]
        have := rd_ne_bot hq μ₁ ν₁
        rw [rd_of_ne_one h.ne'] at this
        unfold PADMPriv.renyiDiv at this
        exact (EReal.add_top_of_ne_bot this).symm
    · have hnac : ¬ μ₁.prod μ₂ ≪ ν₁.prod ν₂ := by
        intro hac
        apply h1
        refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
        have := hac (s := s ×ˢ Set.univ) (by rw [Measure.prod_prod, h0, zero_mul])
        rw [Measure.prod_prod] at this
        simpa using this
      rw [if_neg hnac, if_neg h1]
      have := rd_ne_bot hq μ₂ ν₂
      rw [rd_of_ne_one h.ne'] at this
      unfold PADMPriv.renyiDiv at this
      exact (EReal.top_add_of_ne_bot this).symm

lemma rd_pi {q : ℝ} (hq : 1 ≤ q) (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (n : ℕ) :
    renyiDivergence q (Measure.pi fun _ : Fin n => P) (Measure.pi fun _ : Fin n => Q) =
      (n : EReal) * renyiDivergence q P Q := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty, Measure.pi_of_empty, rd_self hq]
    simp
  | succ n ih =>
    have eP := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).map_eq
    have eQ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) 0).map_eq
    rw [← rd_map_equiv hq (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0),
      eP, eQ, rd_prod hq, ih]
    rw [Nat.cast_succ, EReal.right_distrib_of_nonneg (by positivity) zero_le_one, one_mul,
      add_comm]

end Fact33ii

open Fact33ii in
theorem solution {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    renyiDivergence q ((Measure.pi fun _ : Fin n => P).prod ν)
        ((Measure.pi fun _ : Fin n => Q).prod ν) =
      (n : EReal) * renyiDivergence q P Q := by
  rw [rd_prod hq, rd_pi hq, rd_self hq, add_zero]
