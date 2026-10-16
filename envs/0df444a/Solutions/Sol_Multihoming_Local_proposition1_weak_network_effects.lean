-- Prove2me | solution 1 for Multihoming.Local.proposition1_weak_network_effects
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:38:10.190681+00:00
-- url     : https://prove2.me/submissions/d88364f5-49fa-4f3c-983e-bb3570fc85dc

import Definitions.Def_Multihoming_Local_Model
namespace Multihoming.Local

lemma mh_price_eq (t μ ei ej : ℝ) (ht : 0 < t) (h0 : 0 ≤ μ) (h1 : μ < t) :
    priceM t μ ei ej = (2 * ei * t ^ 2 - ej * μ * t - ei * μ ^ 2 - μ ^ 3 - μ ^ 2 * t
      + 2 * μ * t ^ 2) / (4 * t ^ 2 - μ ^ 2) := by
  unfold priceM
  have hA : (2 * t - μ) ≠ 0 := by intro h; linarith
  have hB : (4 * t ^ 2 - μ ^ 2) ≠ 0 := by nlinarith
  have hC : (2 * t + μ) ≠ 0 := by intro h; linarith
  have hf : (4 * t ^ 2 - μ ^ 2) = (2 * t - μ) * (2 * t + μ) := by ring
  rw [hf]
  field_simp
  ring

lemma mh_foc (t μ ei ej : ℝ) (ht : 0 < t) (h0 : 0 ≤ μ) (h1 : μ < t) :
    2 * t * priceM t μ ei ej - μ * priceM t μ ej ei = μ * (t - μ) + t * ei - μ * ej := by
  rw [mh_price_eq t μ ei ej ht h0 h1, mh_price_eq t μ ej ei ht h0 h1]
  have hB : (4 * t ^ 2 - μ ^ 2) ≠ 0 := by nlinarith
  rw [mul_div_assoc', mul_div_assoc', div_sub_div_same, div_eq_iff hB]
  ring

lemma mh_out_eq (t μ ei ej : ℝ) (ht : 0 < t) (h0 : 0 ≤ μ) (h1 : μ < t) :
    outM t μ ei ej = t * priceM t μ ei ej / (t ^ 2 - μ ^ 2) := by
  have hfoc := mh_foc t μ ei ej ht h0 h1
  unfold outM demandM
  have hA : (t + μ) ≠ 0 := by intro h; linarith
  have hE : (t - μ) ≠ 0 := by intro h; linarith
  have hg : (t ^ 2 - μ ^ 2) = (t - μ) * (t + μ) := by ring
  have hm : μ / (t + μ) = μ * (t - μ) / ((t - μ) * (t + μ)) := by
    rw [mul_comm (t - μ) (t + μ), mul_div_mul_right _ _ hE]
  rw [hg, hm, ← add_div, div_sub_div_same]
  congr 1
  linear_combination (-1 : ℝ) * hfoc

lemma mh_price_mono (t ei ej δ : ℝ) (ht : 0 < t) (hei : 0 < ei) (hei2 : ei < 2 * t)
    (hej : 0 < ej) (hej2 : ej < 2 * t) (hδ0 : 0 < δ) (hδ1 : δ ≤ t / 2)
    (hδ2 : 8 * δ ≤ 2 * t - ej) :
    StrictMonoOn (fun μ => priceM t μ ei ej) (Set.Icc 0 δ) := by
  intro μ hμ ν hν hlt
  obtain ⟨hμ0, hμ1⟩ := hμ
  obtain ⟨hν0, hν1⟩ := hν
  simp only
  rw [mh_price_eq t μ ei ej ht hμ0 (by linarith), mh_price_eq t ν ei ej ht hν0 (by linarith)]
  have hDμ : 0 < 4 * t ^ 2 - μ ^ 2 := by nlinarith
  have hDν : 0 < 4 * t ^ 2 - ν ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ hDμ hDν]
  set Q := -2*ei*μ*t^2 - 2*ei*ν*t^2 - ej*μ*ν*t - 4*ej*t^3 + μ^2*ν^2 - 4*μ^2*t^2
    - 2*μ*ν*t^2 - 4*μ*t^3 - 4*ν^2*t^2 - 4*ν*t^3 + 8*t^4 with hQ
  have key : (2 * ei * t ^ 2 - ej * ν * t - ei * ν ^ 2 - ν ^ 3 - ν ^ 2 * t + 2 * ν * t ^ 2)
      * (4 * t ^ 2 - μ ^ 2) - (2 * ei * t ^ 2 - ej * μ * t - ei * μ ^ 2 - μ ^ 3 - μ ^ 2 * t
      + 2 * μ * t ^ 2) * (4 * t ^ 2 - ν ^ 2) = (ν - μ) * Q := by rw [hQ]; ring
  have t2 : 0 < t ^ 2 := by positivity
  have t3 : 0 < t ^ 3 := by positivity
  have hμδ : μ ≤ δ := hμ1
  have hνδ : ν ≤ δ := hν1
  have b1 : 2*ei*μ*t^2 ≤ 4*t^3*δ := by
    have : ei * μ ≤ 2 * t * δ := by nlinarith
    nlinarith
  have b2 : 2*ei*ν*t^2 ≤ 4*t^3*δ := by
    have : ei * ν ≤ 2 * t * δ := by nlinarith
    nlinarith
  have hμν : μ * ν ≤ t * δ := by nlinarith
  have b3 : ej*μ*ν*t ≤ 2*t^3*δ := by
    have : ej * (μ * ν) ≤ 2 * t * (t * δ) := by
      apply mul_le_mul (le_of_lt hej2) hμν (by positivity) (by positivity)
    nlinarith
  have b4 : 4*μ^2*t^2 ≤ 4*t^3*δ := by
    have : μ ^ 2 ≤ t * δ := by nlinarith
    nlinarith
  have b5 : 4*ν^2*t^2 ≤ 4*t^3*δ := by
    have : ν ^ 2 ≤ t * δ := by nlinarith
    nlinarith
  have b6 : 2*μ*ν*t^2 ≤ 2*t^3*δ := by nlinarith
  have b7 : 4*μ*t^3 ≤ 4*t^3*δ := by nlinarith
  have b8 : 4*ν*t^3 ≤ 4*t^3*δ := by nlinarith
  have b9 : 0 ≤ μ^2*ν^2 := by positivity
  have hQpos : 0 < Q := by
    rw [hQ]
    have h28 : 28 * δ < 4 * (2 * t - ej) := by linarith
    have : t^3 * (28 * δ) < t^3 * (4 * (2 * t - ej)) := mul_lt_mul_of_pos_left h28 t3
    linarith
  have : 0 < (ν - μ) * Q := mul_pos (by linarith) hQpos
  linarith

lemma mh_all (t ei ej δ : ℝ) (ht : 0 < t) (hei : 0 < ei) (hei2 : ei < 2 * t)
    (hej : 0 < ej) (hej2 : ej < 2 * t) (hδ0 : 0 < δ) (hδ1 : δ ≤ t / 2)
    (hδ2 : 8 * δ ≤ 2 * t - ej) :
    StrictMonoOn (fun μ => outM t μ ei ej) (Set.Icc 0 δ) ∧
    StrictMonoOn (fun μ => priceM t μ ei ej) (Set.Icc 0 δ) ∧
    StrictMonoOn (fun μ => profitM t μ ei ej) (Set.Icc 0 δ) := by
  have hp := mh_price_mono t ei ej δ ht hei hei2 hej hej2 hδ0 hδ1 hδ2
  have h0mem : (0:ℝ) ∈ Set.Icc 0 δ := ⟨le_refl _, le_of_lt hδ0⟩
  have hp0 : priceM t 0 ei ej = ei / 2 := by
    unfold priceM; field_simp; ring
  have ppos : ∀ μ ∈ Set.Icc (0:ℝ) δ, 0 < priceM t μ ei ej := by
    intro μ hμ
    rcases eq_or_lt_of_le hμ.1 with h | h
    · subst h; rw [hp0]; linarith
    · have := hp h0mem hμ h; simp only at this; rw [hp0] at this; linarith
  have hout : ∀ μ ν, μ ∈ Set.Icc (0:ℝ) δ → ν ∈ Set.Icc (0:ℝ) δ → μ < ν →
      outM t μ ei ej < outM t ν ei ej ∧ 0 < outM t μ ei ej := by
    intro μ ν hμ hν hlt
    have hpl := hp hμ hν hlt; simp only at hpl
    have pμ := ppos μ hμ
    have pν := ppos ν hν
    obtain ⟨hμ0, hμ1⟩ := hμ
    obtain ⟨hν0, hν1⟩ := hν
    rw [mh_out_eq t μ ei ej ht hμ0 (by linarith), mh_out_eq t ν ei ej ht hν0 (by linarith)]
    have hDμ : 0 < t ^ 2 - μ ^ 2 := by nlinarith
    have hDν : 0 < t ^ 2 - ν ^ 2 := by nlinarith
    refine ⟨?_, by positivity⟩
    rw [div_lt_div_iff₀ hDμ hDν]
    have : t ^ 2 - ν ^ 2 ≤ t ^ 2 - μ ^ 2 := by nlinarith
    have e1 : t * priceM t μ ei ej * (t ^ 2 - ν ^ 2) < t * priceM t ν ei ej * (t ^ 2 - ν ^ 2) := by
      apply mul_lt_mul_of_pos_right _ hDν
      exact mul_lt_mul_of_pos_left hpl ht
    have e2 : t * priceM t ν ei ej * (t ^ 2 - ν ^ 2) ≤ t * priceM t ν ei ej * (t ^ 2 - μ ^ 2) := by
      apply mul_le_mul_of_nonneg_left this; positivity
    linarith
  refine ⟨fun μ hμ ν hν hlt => (hout μ ν hμ hν hlt).1, hp, ?_⟩
  intro μ hμ ν hν hlt
  simp only [profitM]
  have h1 := hout μ ν hμ hν hlt
  have hpl := hp hμ hν hlt; simp only at hpl
  have pμ := ppos μ hμ
  exact mul_lt_mul'' hpl h1.1 (le_of_lt pμ) (le_of_lt h1.2)

theorem proposition1_weak_network_effects (t e0 e1 : ℝ) (ht : 0 < t)
    (h0 : e0 < 2 * t) (h1 : e1 < 2 * t) (hpm : 2 * t < e0 + e1) :
    ∃ δ, 0 < δ ∧ δ < t ∧
      (StrictMonoOn (fun μ => outM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => outM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictAntiOn (fun μ => singleM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictAntiOn (fun μ => singleM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => priceM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => priceM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => profitM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => profitM t μ e1 e0) (Set.Icc 0 δ)) := by
  have he0 : 0 < e0 := by linarith
  have he1 : 0 < e1 := by linarith
  set δ := min (t / 2) (min ((2 * t - e0) / 8) ((2 * t - e1) / 8)) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]; apply lt_min (by linarith); apply lt_min <;> linarith
  have hδ1 : δ ≤ t / 2 := min_le_left _ _
  have hδa : δ ≤ (2 * t - e0) / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδb : δ ≤ (2 * t - e1) / 8 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨A1, A2, A3⟩ := mh_all t e0 e1 δ ht he0 h0 he1 h1 hδ0 hδ1 (by linarith)
  obtain ⟨B1, B2, B3⟩ := mh_all t e1 e0 δ ht he1 h1 he0 h0 hδ0 hδ1 (by linarith)
  refine ⟨δ, hδ0, by linarith, ⟨A1, B1⟩, ⟨?_, ?_⟩, ⟨A2, B2⟩, ⟨A3, B3⟩⟩
  · intro μ hμ ν hν hlt
    have := B1 hμ hν hlt
    simp only [singleM] at this ⊢
    linarith
  · intro μ hμ ν hν hlt
    have := A1 hμ hν hlt
    simp only [singleM] at this ⊢
    linarith

end Multihoming.Local


-- Platform entry point: restates the target verbatim.
namespace Multihoming.Local

/-- Proposition 1, PDF p. 19: under partial multihoming at `μ = 0` (`e₀, e₁ < 2t < e₀ + e₁`),
there is `δ ∈ (0, t)` such that on `[0, δ]` each good's total demand, price and profit at the
candidate prices (16) strictly increase in `μ`, and each good's singlehomers strictly decrease. -/
theorem _root_.solution (t e0 e1 : ℝ) (ht : 0 < t)
    (h0 : e0 < 2 * t) (h1 : e1 < 2 * t) (hpm : 2 * t < e0 + e1) :
    ∃ δ, 0 < δ ∧ δ < t ∧
      (StrictMonoOn (fun μ => outM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => outM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictAntiOn (fun μ => singleM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictAntiOn (fun μ => singleM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => priceM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => priceM t μ e1 e0) (Set.Icc 0 δ)) ∧
      (StrictMonoOn (fun μ => profitM t μ e0 e1) (Set.Icc 0 δ) ∧
        StrictMonoOn (fun μ => profitM t μ e1 e0) (Set.Icc 0 δ)) := by
  apply @Multihoming.Local.proposition1_weak_network_effects <;> assumption

end Multihoming.Local
