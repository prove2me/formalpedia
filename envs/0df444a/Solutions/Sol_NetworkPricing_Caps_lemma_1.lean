-- Prove2me | solution 1 for NetworkPricing.Caps.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:56:09.156312+00:00
-- url     : https://prove2.me/submissions/887e671b-82cf-49a7-8b3d-9648b15697d2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

open KellyStochasticNetworks NetworkPricing.Caps
open Filter Topology Set

namespace NPCAux

variable {J R Sd : ℕ}

lemma int_diff_ge (φ : ℝ → ℝ) (M a b : ℝ) (hanti : AntitoneOn φ (Icc 0 M))
    (hc : ContinuousOn φ (Icc 0 M)) (ha : a ∈ Icc 0 M) (hb : b ∈ Icc 0 M) :
    (b - a) * φ b ≤ (∫ s in (0:ℝ)..b, φ s) - ∫ s in (0:ℝ)..a, φ s := by
  have h0 : (0:ℝ) ∈ Icc 0 M := ⟨le_rfl, ha.1.trans ha.2⟩
  have hi : ∀ x ∈ Icc 0 M, ∀ y ∈ Icc 0 M, IntervalIntegrable φ MeasureTheory.volume x y :=
    fun x hx y hy => (hc.mono (Set.uIcc_subset_Icc hx hy)).intervalIntegrable
  rw [intervalIntegral.integral_interval_sub_left (hi 0 h0 b hb) (hi 0 h0 a ha)]
  rcases le_total a b with hab | hba
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (hi a ha b hb)
      (fun x hx => hanti ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩ hb hx.2)
    simpa [intervalIntegral.integral_const] using this
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on hba (hi b hb a ha) intervalIntegrable_const
      (fun x hx => hanti hb ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩ hx.1)
    simp [intervalIntegral.integral_const] at this
    linarith

lemma int_diff_le (φ : ℝ → ℝ) (a b : ℝ) (hmono : MonotoneOn φ (Ici 0))
    (hc : Continuous φ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ s in (0:ℝ)..b, φ s) - (∫ s in (0:ℝ)..a, φ s) ≤ (b - a) * φ b := by
  have hi : ∀ x y : ℝ, IntervalIntegrable φ MeasureTheory.volume x y :=
    fun x y => hc.intervalIntegrable x y
  rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  rcases le_total a b with hab | hba
  · have := intervalIntegral.integral_mono_on hab (hi _ _)
      intervalIntegrable_const
      (fun x hx => hmono (show (0:ℝ) ≤ x from ha.trans hx.1) (show (0:ℝ) ≤ b from hb) hx.2)
    simpa [intervalIntegral.integral_const] using this
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on hba intervalIntegrable_const
      (hi _ _)
      (fun x hx => hmono (show (0:ℝ) ≤ b from hb) (show (0:ℝ) ≤ x from hb.trans hx.1) hx.1)
    simp [intervalIntegral.integral_const] at this
    linarith

lemma linkFlow_nonneg (I : Instance J R Sd) (hA : ∀ e q, I.A e q = 0 ∨ I.A e q = 1)
    {f : Fin R → ℝ} (hf : ∀ q, 0 ≤ f q) (e : Fin J) : 0 ≤ linkFlow I.A f e := by
  unfold linkFlow
  apply Finset.sum_nonneg
  intro q _
  rcases hA e q with h | h <;> simp [h, hf q]

lemma demand_nonneg (I : Instance J R Sd) {f : Fin R → ℝ} (hf : ∀ q, 0 ≤ f q) (k : Fin Sd) :
    0 ≤ I.demand f k :=
  Finset.sum_nonneg (fun q _ => hf q)

lemma linkFlow_comb (A : Fin J → Fin R → ℝ) (f g : Fin R → ℝ) (c : ℝ) (e : Fin J) :
    linkFlow A (fun q => f q + c * (g q - f q)) e
      = linkFlow A f e + c * (linkFlow A g e - linkFlow A f e) := by
  unfold linkFlow
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  · apply Finset.sum_congr rfl; intro q _; ring

lemma demand_comb (I : Instance J R Sd) (f g : Fin R → ℝ) (c : ℝ) (k : Fin Sd) :
    I.demand (fun q => f q + c * (g q - f q)) k
      = I.demand f k + c * (I.demand g k - I.demand f k) := by
  unfold Instance.demand
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma feasible_comb (I : Instance J R Sd) {f g : Fin R → ℝ} (hf : I.Feasible f)
    (hg : I.Feasible g) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    I.Feasible (fun q => f q + c * (g q - f q)) := by
  refine ⟨fun q => ?_, fun k => ?_⟩
  · have h1 := hf.1 q; have h2 := hg.1 q
    nlinarith
  · rw [demand_comb]
    have h1 := hf.2 k; have h2 := hg.2 k
    nlinarith

/-- First-order optimality condition of a Wardrop flow (maximizer of the potential (1)). -/
lemma foc (I : Instance J R Sd) (hI : I.Standing) (t : Fin J → ℝ) {f g : Fin R → ℝ}
    (hf : I.IsWardropFlow t f) (hg : I.Feasible g) :
    (∑ k, (I.demand g k - I.demand f k) * I.u k (I.demand f k))
      - ∑ e, (linkFlow I.A g e - linkFlow I.A f e) * (I.ℓ e (linkFlow I.A f e) + t e) ≤ 0 := by
  obtain ⟨hA, hr, hanti, hcont, hu0, hmono, hconv, hdiff, hl0⟩ := hI
  set r := fun k => I.demand f k with hr_def
  set Δ := fun k => I.demand g k - I.demand f k with hΔ
  set x := fun e => linkFlow I.A f e with hx
  set δ := fun e => linkFlow I.A g e - linkFlow I.A f e with hδ
  let F : ℝ → ℝ := fun c =>
    (∑ k, Δ k * I.u k (r k + c * Δ k)) - ∑ e, δ e * (I.ℓ e (x e + c * δ e) + t e)
  have hrmem : ∀ k, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → r k + c * Δ k ∈ Icc 0 (I.r k) := by
    intro k c hc0 hc1
    have := (feasible_comb I hf.1 hg hc0 hc1)
    rw [← demand_comb]
    exact ⟨demand_nonneg I this.1 k, this.2 k⟩
  have hxnn : ∀ e, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → 0 ≤ x e + c * δ e := by
    intro e c hc0 hc1
    have := (feasible_comb I hf.1 hg hc0 hc1)
    rw [← linkFlow_comb]
    exact linkFlow_nonneg I hA this.1 e
  -- F c ≤ 0 for c ∈ (0,1]
  have hF : ∀ c ∈ Ioc (0:ℝ) 1, F c ≤ 0 := by
    rintro c ⟨hc0, hc1⟩
    have hfeas := feasible_comb I hf.1 hg hc0.le hc1
    have hle := hf.2 _ hfeas
    unfold Instance.potential at hle
    simp only [demand_comb, linkFlow_comb] at hle
    have hU : ∀ k, (c * Δ k) * I.u k (r k + c * Δ k) ≤
        I.U k (r k + c * Δ k) - I.U k (r k) := by
      intro k
      have := int_diff_ge (I.u k) (I.r k) (r k) (r k + c * Δ k) (hanti k) (hcont k)
        (by simpa using hrmem k 0 le_rfl zero_le_one) (hrmem k c hc0.le hc1)
      unfold Instance.U
      convert this using 2; ring
    have hL : ∀ e, (∫ y in (0:ℝ)..(x e + c * δ e), (I.ℓ e y + t e))
        - (∫ y in (0:ℝ)..(x e), (I.ℓ e y + t e)) ≤ (c * δ e) * (I.ℓ e (x e + c * δ e) + t e) := by
      intro e
      have := int_diff_le (fun y => I.ℓ e y + t e) (x e) (x e + c * δ e)
        (fun a ha b hb hab => by simpa using hmono e ha hb hab)
        ((hdiff e).continuous.add continuous_const)
        (by simpa using hxnn e 0 le_rfl zero_le_one) (hxnn e c hc0.le hc1)
      convert this using 2; ring
    have hsumU := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hU k)
    have hsumL := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hL e)
    rw [Finset.sum_sub_distrib] at hsumU hsumL
    have hcF : c * F c ≤ 0 := by
      have e1 : c * F c = (∑ k, (c * Δ k) * I.u k (r k + c * Δ k))
          - ∑ e, (c * δ e) * (I.ℓ e (x e + c * δ e) + t e) := by
        simp only [F, mul_sub, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
      rw [e1]
      simp only [r, Δ, x, δ] at hsumU hsumL hle ⊢
      linarith
    by_contra hpos
    push Not at hpos
    have := mul_pos hc0 hpos
    linarith
  -- pass to the limit c → 0⁺
  have hlim : Tendsto F (𝓝[Ioc (0:ℝ) 1] 0) (𝓝 (F 0)) := by
    apply Tendsto.sub
    · apply tendsto_finsetSum
      intro k _
      apply Tendsto.const_mul
      have h1 : ContinuousWithinAt (fun c : ℝ => r k + c * Δ k) (Ioc (0:ℝ) 1) 0 :=
        (continuous_const.add (continuous_id.mul continuous_const)).continuousWithinAt
      have h2 : ContinuousWithinAt (I.u k) (Icc 0 (I.r k)) ((fun c : ℝ => r k + c * Δ k) 0) :=
        hcont k _ (hrmem k 0 le_rfl zero_le_one)
      exact (ContinuousWithinAt.comp (f := fun c : ℝ => r k + c * Δ k) h2 h1
        (fun c hc => hrmem k c hc.1.le hc.2)).tendsto
    · apply tendsto_finsetSum
      intro e _
      apply Tendsto.const_mul
      apply Tendsto.add_const
      have hc : Continuous (fun c : ℝ => I.ℓ e (x e + c * δ e)) :=
        (hdiff e).continuous.comp (continuous_const.add (continuous_id.mul continuous_const))
      exact hc.continuousWithinAt.tendsto
  have := left_nhdsWithin_Ioc_neBot (show (0:ℝ) < 1 from one_pos)
  have h0 : F 0 ≤ 0 := le_of_tendsto hlim (eventually_nhdsWithin_of_forall hF)
  simpa [F, r, Δ, x, δ] using h0

lemma mono_term (φ : ℝ → ℝ) (hmono : MonotoneOn φ (Ici 0)) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : 0 ≤ (b - a) * (φ b - φ a) := by
  rcases le_total a b with hab | hba
  · exact mul_nonneg (by linarith) (by linarith [hmono (show a ∈ Ici 0 from ha) (show b ∈ Ici 0 from hb) hab])
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
      (by linarith [hmono (show b ∈ Ici 0 from hb) (show a ∈ Ici 0 from ha) hba])

/-- The summed variational inequality behind Lemma 1. -/
lemma core (I : Instance J R Sd) (hI : I.Standing) (t t' : Fin J → ℝ) {f f' : Fin R → ℝ}
    (hf : I.IsWardropFlow t f) (hf' : I.IsWardropFlow t' f') :
    ∑ e, (linkFlow I.A f' e - linkFlow I.A f e) *
      (I.ℓ e (linkFlow I.A f' e) + t' e - I.ℓ e (linkFlow I.A f e) - t e) ≤ 0 := by
  have h1 := foc I hI t hf hf'.1
  have h2 := foc I hI t' hf' hf.1
  obtain ⟨hA, hr, hanti, hcont, hu0, hmono, hconv, hdiff, hl0⟩ := hI
  have hU : ∑ k, (I.demand f' k - I.demand f k) *
      (I.u k (I.demand f' k) - I.u k (I.demand f k)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    have m1 : I.demand f k ∈ Icc 0 (I.r k) := ⟨demand_nonneg I hf.1.1 k, hf.1.2 k⟩
    have m2 : I.demand f' k ∈ Icc 0 (I.r k) := ⟨demand_nonneg I hf'.1.1 k, hf'.1.2 k⟩
    rcases le_total (I.demand f k) (I.demand f' k) with h | h
    · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [hanti k m1 m2 h])
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hanti k m2 m1 h])
  have eqU : (∑ k, (I.demand f' k - I.demand f k) * I.u k (I.demand f k))
      + (∑ k, (I.demand f k - I.demand f' k) * I.u k (I.demand f' k))
      = - ∑ k, (I.demand f' k - I.demand f k) *
      (I.u k (I.demand f' k) - I.u k (I.demand f k)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have eqL : (∑ e, (linkFlow I.A f' e - linkFlow I.A f e) * (I.ℓ e (linkFlow I.A f e) + t e))
      + (∑ e, (linkFlow I.A f e - linkFlow I.A f' e) * (I.ℓ e (linkFlow I.A f' e) + t' e))
      = - ∑ e, (linkFlow I.A f' e - linkFlow I.A f e) *
      (I.ℓ e (linkFlow I.A f' e) + t' e - I.ℓ e (linkFlow I.A f e) - t e) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  linarith

end NPCAux

open NPCAux in
theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (t t' : Fin J → ℝ) (ht : 0 ≤ t) (ht' : 0 ≤ t') (htt' : t ≤ t') (hne : ∃ e, t e < t' e) :
    (∃ e₁, t e₁ < t' e₁ ∧ linkFlow I.A (flow t') e₁ ≤ linkFlow I.A (flow t) e₁) ∧
    (∃ e₂, t e₂ < t' e₂ ∧
      (linkFlow I.A (flow t') e₂ - linkFlow I.A (flow t) e₂) *
        (I.ℓ e₂ (linkFlow I.A (flow t') e₂) + t' e₂
          - I.ℓ e₂ (linkFlow I.A (flow t) e₂) - t e₂) ≤ 0) := by
  have hf := hflow t ht
  have hf' := hflow t' ht'
  have hS := core I hI t t' hf hf'
  have hA := hI.1
  have hmono := hI.2.2.2.2.2.1
  set x := fun e => linkFlow I.A (flow t) e with hx
  set y := fun e => linkFlow I.A (flow t') e with hy
  have hxn : ∀ e, 0 ≤ x e := fun e => linkFlow_nonneg I hA hf.1.1 e
  have hyn : ∀ e, 0 ≤ y e := fun e => linkFlow_nonneg I hA hf'.1.1 e
  have hterm : ∀ e, 0 ≤ (y e - x e) * (I.ℓ e (y e) - I.ℓ e (x e)) :=
    fun e => mono_term (I.ℓ e) (hmono e) (hxn e) (hyn e)
  have hoff : ∀ e, ¬ t e < t' e → 0 ≤ (y e - x e) * (I.ℓ e (y e) + t' e - I.ℓ e (x e) - t e) := by
    intro e he
    have : t' e = t e := le_antisymm (not_lt.mp he) (htt' e)
    rw [this]
    have := hterm e
    linarith [show (y e - x e) * (I.ℓ e (y e) + t e - I.ℓ e (x e) - t e)
      = (y e - x e) * (I.ℓ e (y e) - I.ℓ e (x e)) by ring]
  obtain ⟨e0, he0⟩ := hne
  constructor
  · by_contra hcon
    push Not at hcon
    have hpos : 0 < ∑ e, (y e - x e) * (I.ℓ e (y e) + t' e - I.ℓ e (x e) - t e) := by
      apply Finset.sum_pos'
      · intro e _
        by_cases h : t e < t' e
        · have h1 := hcon e h
          have h2 := hterm e
          have : 0 ≤ I.ℓ e (y e) - I.ℓ e (x e) := by
            by_contra hc; push Not at hc; nlinarith
          nlinarith
        · exact hoff e h
      · refine ⟨e0, Finset.mem_univ _, ?_⟩
        have h1 := hcon e0 he0
        have h2 := hterm e0
        have : 0 ≤ I.ℓ e0 (y e0) - I.ℓ e0 (x e0) := by
          by_contra hc; push Not at hc; nlinarith
        have : 0 < y e0 - x e0 := by linarith
        nlinarith
    exact absurd hS (not_le.mpr hpos)
  · by_contra hcon
    push Not at hcon
    have hpos : 0 < ∑ e, (y e - x e) * (I.ℓ e (y e) + t' e - I.ℓ e (x e) - t e) := by
      apply Finset.sum_pos'
      · intro e _
        by_cases h : t e < t' e
        · exact (hcon e h).le
        · exact hoff e h
      · exact ⟨e0, Finset.mem_univ _, hcon e0 he0⟩
    exact absurd hS (not_le.mpr hpos)
