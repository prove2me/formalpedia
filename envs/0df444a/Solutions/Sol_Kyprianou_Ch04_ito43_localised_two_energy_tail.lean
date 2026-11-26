-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_localised_two_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:30:33.912615+00:00
-- url     : https://prove2.me/submissions/3828bdc7-5160-4237-a72f-e87122e9f026

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A uniform error bounded by two localised energies has a small outer-probability tail. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : NNReal) (U V : Set Ω) (Q E : ℕ → NNReal → Ω → ℝ) (J : Ω → ℝ)
    (C D a e eta : ℝ) (ha : 0 ≤ a) (hsmall : a*(C+D) < e)
    (hU : (P U).toReal ≤ eta/3) (hV : (P V).toReal ≤ eta/3)
    (hQ : ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, C ≤ Q n t w}).toReal ≤ eta/3)
    (hgood : ∀ᵐ w ∂P, w ∉ U → w ∉ V →
      J w ≤ D ∧ ∀ n t, t ≤ T → |E n t w| ≤ a*(Q n t w+J w)) :
    ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal ≤ eta := by
  filter_upwards [hQ] with n hQn
  let W : Set Ω := {w | ∃ t ≤ T, C ≤ Q n t w}
  let B : Set Ω := {w | ∃ t ≤ T, e ≤ |E n t w|}
  have hsub : ∀ᵐ w ∂P, w ∈ B → w ∈ U ∪ V ∪ W := by
    filter_upwards [hgood] with w hw
    rintro ⟨t,ht,hE⟩
    by_contra hb
    obtain ⟨hJ,hbound⟩ := hw (fun h => hb (Or.inl (Or.inl h)))
      (fun h => hb (Or.inl (Or.inr h)))
    have hC : Q n t w < C := lt_of_not_ge (fun h => hb (Or.inr ⟨t,ht,h⟩))
    have H := (hbound n t ht).trans
      (mul_le_mul_of_nonneg_left (add_le_add hC.le hJ) ha)
    exact (not_lt_of_ge (hE.trans H)) hsmall
  have H1 := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have H2 : (P (U ∪ V ∪ W)).toReal ≤ (P U).toReal+(P V).toReal+(P W).toReal :=
    (measureReal_union_le (U ∪ V) W).trans (add_le_add_left (measureReal_union_le U V) _)
  exact (H1.trans H2).trans (by linarith [hU,hV,hQn])
