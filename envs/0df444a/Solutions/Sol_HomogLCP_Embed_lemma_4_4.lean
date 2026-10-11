-- Prove2me | solution 1 for HomogLCP.Embed.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:25:48.342603+00:00
-- url     : https://prove2.me/submissions/715a752c-9a18-4bb5-a2c0-779532680179

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace RRAux_HomogLCP_Embed_lemma_4_4

open Matrix HomogLCP.Embed Filter Topology

variable {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)

lemma trans_dot (y z : Fin d → ℝ) : y ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]

lemma Qnn (hM : (M + Mᵀ).PosSemidef) (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  have h := hM.dotProduct_mulVec_nonneg v
  rw [star_trivial, add_mulVec, dotProduct_add, ← trans_dot] at h
  linarith

lemma Qker (hM : (M + Mᵀ).PosSemidef) (v : Fin d → ℝ) (hv : v ⬝ᵥ (M *ᵥ v) = 0) :
    Mᵀ *ᵥ v = -(M *ᵥ v) := by
  have h : star v ⬝ᵥ ((M + Mᵀ) *ᵥ v) = 0 := by
    rw [star_trivial, add_mulVec, dotProduct_add, ← trans_dot, hv, add_zero]
  have h2 := (hM.dotProduct_mulVec_zero_iff v).1 h
  rw [add_mulVec] at h2
  exact eq_neg_of_add_eq_zero_right h2

lemma self_nonneg (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := by
  have := dotProduct_star_self_nonneg v
  rwa [star_trivial] at this

lemma FF (hM : (M + Mᵀ).PosSemidef) (z y : Fin d → ℝ) (τ s : ℝ) (hτ : 0 < τ) (hs : 0 < s) :
    0 ≤ (M *ᵥ z + τ • q - (M *ᵥ y + s • q)) ⬝ᵥ (z - y) +
      ((-(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - (-(y ⬝ᵥ (M *ᵥ y)) / s - y ⬝ᵥ q)) * (τ - s) := by
  have key : (M *ᵥ z + τ • q - (M *ᵥ y + s • q)) ⬝ᵥ (z - y) +
      ((-(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - (-(y ⬝ᵥ (M *ᵥ y)) / s - y ⬝ᵥ q)) * (τ - s)
      = τ * s * ((τ⁻¹ • z - s⁻¹ • y) ⬝ᵥ (M *ᵥ (τ⁻¹ • z - s⁻¹ • y))) := by
    simp only [mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub, sub_dotProduct,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (M *ᵥ z) z, dotProduct_comm (M *ᵥ z) y, dotProduct_comm (M *ᵥ y) z,
      dotProduct_comm (M *ᵥ y) y, dotProduct_comm q z, dotProduct_comm q y]
    field_simp
    ring
  rw [key]
  exact mul_nonneg (mul_nonneg hτ.le hs.le) (Qnn M hM _)

lemma FI (hM : (M + Mᵀ).PosSemidef) (z y : Fin d → ℝ) (τ κ' : ℝ) (hτ : 0 < τ)
    (hy : y ⬝ᵥ (M *ᵥ y) = 0) (hκ : κ' ≤ -(y ⬝ᵥ q)) :
    0 ≤ (M *ᵥ z + τ • q - M *ᵥ y) ⬝ᵥ (z - y) +
      ((-(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - κ') * (τ - 0) := by
  have hker := Qker M hM y hy
  have hc : y ⬝ᵥ (M *ᵥ z) = -(z ⬝ᵥ (M *ᵥ y)) := by
    rw [trans_dot, hker, dotProduct_neg]
  have key : (M *ᵥ z + τ • q - M *ᵥ y) ⬝ᵥ (z - y) +
      ((-(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - κ') * (τ - 0) = -τ * (y ⬝ᵥ q + κ') := by
    simp only [mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub, sub_dotProduct,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (M *ᵥ z) z, dotProduct_comm (M *ᵥ z) y, dotProduct_comm (M *ᵥ y) z,
      dotProduct_comm (M *ᵥ y) y, dotProduct_comm q z, dotProduct_comm q y, hc, hy]
    field_simp
    ring
  rw [key]
  have : 0 ≤ -(y ⬝ᵥ q + κ') := by linarith
  nlinarith

lemma II (hM : (M + Mᵀ).PosSemidef) (z y : Fin d → ℝ) (κ κ' : ℝ) :
    0 ≤ (M *ᵥ z - M *ᵥ y) ⬝ᵥ (z - y) + (κ - κ') * (0 - 0) := by
  rw [sub_self, mul_zero, add_zero, ← mulVec_sub, dotProduct_comm]
  exact Qnn M hM _

lemma pair_swap (u u' v v' : (Fin d → ℝ) × ℝ) :
    pair (u - u') (v - v') = pair (u' - u) (v' - v) := by
  simp only [pair, Prod.fst_sub, Prod.snd_sub]
  rw [← neg_sub u.1 u'.1, ← neg_sub v.1 v'.1, neg_dotProduct, dotProduct_neg, neg_neg]
  ring

lemma mono (hM : (M + Mᵀ).PosSemidef) : IsMonotoneOp (embQ M q) := by
  have FIsym : ∀ a ∈ embF M q, ∀ b ∈ embI M q, 0 ≤ pair (a.2 - b.2) (a.1 - b.1) := by
    rintro ⟨⟨z, τ⟩, w, κ⟩ ⟨hτ, ha⟩ ⟨⟨y, s⟩, w', κ'⟩ ⟨hs, hy, hw', hκ'⟩
    simp only [Prod.mk.injEq] at ha hs hy hw' hκ' hτ
    obtain ⟨rfl, rfl⟩ := ha
    subst hs hw'
    simpa [pair] using FI M q hM z y τ κ' hτ hy hκ'
  rintro a (ha | ha) b (hb | hb)
  · obtain ⟨⟨z, τ⟩, w, κ⟩ := a
    obtain ⟨⟨y, s⟩, w', κ'⟩ := b
    obtain ⟨hτ, ha⟩ := ha
    obtain ⟨hs, hb⟩ := hb
    simp only [Prod.mk.injEq] at ha hb hτ hs
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := hb
    simpa [pair] using FF M q hM z y τ s hτ hs
  · exact FIsym a ha b hb
  · rw [pair_swap]; exact FIsym b hb a ha
  · obtain ⟨⟨z, τ⟩, w, κ⟩ := a
    obtain ⟨⟨y, s⟩, w', κ'⟩ := b
    obtain ⟨hτ, -, hw, -⟩ := ha
    obtain ⟨hs, -, hw', -⟩ := hb
    simp only at hτ hs hw hw'
    subst hτ hs hw hw'
    simpa [pair] using II M hM z y κ κ'

lemma affine_nonneg (A c : ℝ) (h : ∀ τ : ℝ, 0 < τ → 0 ≤ A + τ * c) : 0 ≤ A ∧ 0 ≤ c := by
  constructor
  · by_contra hA
    push Not at hA
    by_cases hc : c ≤ 0
    · have := h 1 one_pos; nlinarith
    · push Not at hc
      have := h (-A / (2 * c)) (div_pos (by linarith) (by linarith))
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hc.ne'] at this
      linarith
  · by_contra hc
    push Not at hc
    have := h ((|A| + 1) / (-c)) (div_pos (by positivity) (by linarith))
    rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hc.ne, mul_neg, mul_one] at this
    have := le_abs_self A
    linarith

lemma key_max (hM : (M + Mᵀ).PosSemidef) (x w : Fin d → ℝ) (σ κ : ℝ)
    (h : ∀ b ∈ embQ M q, 0 ≤ pair ((w, κ) - b.2) ((x, σ) - b.1)) :
    ((x, σ), (w, κ)) ∈ embQ M q := by
  rcases lt_trichotomy σ 0 with hσ | hσ | hσ
  · -- σ < 0
    exfalso
    set T := (|w ⬝ᵥ x| + 1) / (-σ) with hT
    have hTpos : 0 < T := div_pos (by positivity) (by linarith)
    set κ' := min 0 (κ - T)
    have hb : ((0, 0), (M *ᵥ 0, κ')) ∈ embQ M q :=
      Or.inr ⟨rfl, by simp, rfl, by simp [κ']⟩
    have := h _ hb
    simp only [pair, Prod.fst_sub, Prod.snd_sub, mulVec_zero, sub_zero] at this
    have h1 : T ≤ κ - κ' := by have := min_le_right 0 (κ - T); linarith
    have h2 : (κ - κ') * σ ≤ T * σ := mul_le_mul_of_nonpos_right h1 hσ.le
    have h3 : T * σ = -(|w ⬝ᵥ x| + 1) := by
      rw [hT, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    have := le_abs_self (w ⬝ᵥ x)
    linarith
  · -- σ = 0
    subst hσ
    have hall : ∀ y : Fin d → ℝ, 0 ≤ w ⬝ᵥ x - y ⬝ᵥ (w + Mᵀ *ᵥ x) ∧ 0 ≤ -(x ⬝ᵥ q) - κ := by
      intro y
      apply affine_nonneg
      intro τ hτ
      have hb : ((y, τ), (M *ᵥ y + τ • q, -(y ⬝ᵥ (M *ᵥ y)) / τ - y ⬝ᵥ q)) ∈ embQ M q :=
        Or.inl ⟨hτ, rfl⟩
      have := h _ hb
      convert this using 1
      simp only [pair, Prod.fst_sub, Prod.snd_sub]
      simp only [dotProduct_add, mulVec_sub, mulVec_add, mulVec_smul, dotProduct_sub,
        sub_dotProduct, add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← trans_dot, dotProduct_comm (M *ᵥ y) x, dotProduct_comm (M *ᵥ y) y,
        dotProduct_comm q x, dotProduct_comm q y, dotProduct_comm w x, dotProduct_comm y w]
      field_simp
      ring
    set β := w + Mᵀ *ᵥ x with hβ
    have hβ0 : β = 0 := by
      by_contra hne
      have hpos : 0 < β ⬝ᵥ β :=
        lt_of_le_of_ne (self_nonneg β) (Ne.symm (fun h => hne (dotProduct_self_eq_zero.1 h)))
      have := (hall (((w ⬝ᵥ x + 1) / (β ⬝ᵥ β)) • β)).1
      rw [smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    have hw : w = -(Mᵀ *ᵥ x) := eq_neg_of_add_eq_zero_left hβ0
    have h0 := (hall 0).1
    simp only [zero_dotProduct, sub_zero] at h0
    rw [hw, neg_dotProduct, dotProduct_comm, ← trans_dot] at h0
    have hQ : x ⬝ᵥ (M *ᵥ x) = 0 := le_antisymm (by linarith) (Qnn M hM x)
    refine Or.inr ⟨rfl, hQ, ?_, by linarith [(hall 0).2]⟩
    show w = M *ᵥ x
    rw [hw, Qker M hM x hQ, neg_neg]
  · -- σ > 0
    set Δ := w - (M *ᵥ x + σ • q) with hΔ
    set δ := κ - (-(x ⬝ᵥ (M *ᵥ x)) / σ - x ⬝ᵥ q) with hδ
    set g : ℝ → ℝ := fun t =>
      (w - (M *ᵥ (x + t • Δ) + (σ + t * δ) • q)) ⬝ᵥ (-Δ) +
        (κ - (-((x + t • Δ) ⬝ᵥ (M *ᵥ (x + t • Δ))) / (σ + t * δ) - (x + t • Δ) ⬝ᵥ q)) * (-δ)
      with hg
    have hcont : ContinuousAt g 0 := by
      have hden : σ + 0 * δ ≠ 0 := by simp; exact hσ.ne'
      simp only [hg]
      apply ContinuousAt.add
      · fun_prop
      · apply ContinuousAt.mul _ continuousAt_const
        apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.sub _ (by fun_prop)
        exact ContinuousAt.div (f := fun t : ℝ => -((x + t • Δ) ⬝ᵥ M *ᵥ (x + t • Δ)))
          (g := fun t : ℝ => σ + t * δ) (by fun_prop) (by fun_prop) hden
    have hden_ev : ∀ᶠ t in 𝓝 (0:ℝ), 0 < σ + t * δ := by
      have : Tendsto (fun t : ℝ => σ + t * δ) (𝓝 0) (𝓝 (σ + 0 * δ)) := by
        exact (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      rw [zero_mul, add_zero] at this
      exact this.eventually (lt_mem_nhds hσ)
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 ≤ g t := by
      filter_upwards [hden_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hden ht
      have ht' : 0 < t := ht
      have hb : ((x + t • Δ, σ + t * δ), (M *ᵥ (x + t • Δ) + (σ + t * δ) • q,
          -((x + t • Δ) ⬝ᵥ (M *ᵥ (x + t • Δ))) / (σ + t * δ) - (x + t • Δ) ⬝ᵥ q)) ∈ embQ M q :=
        Or.inl ⟨hden, rfl⟩
      have := h _ hb
      have e : pair ((w, κ) - (M *ᵥ (x + t • Δ) + (σ + t * δ) • q,
          -((x + t • Δ) ⬝ᵥ (M *ᵥ (x + t • Δ))) / (σ + t * δ) - (x + t • Δ) ⬝ᵥ q))
          ((x, σ) - (x + t • Δ, σ + t * δ)) = t * g t := by
        simp only [pair, Prod.fst_sub, Prod.snd_sub, hg]
        have e1 : x - (x + t • Δ) = t • (-Δ) := by rw [smul_neg]; abel
        rw [e1, dotProduct_smul, smul_eq_mul]
        ring
      rw [e] at this
      exact nonneg_of_mul_nonneg_right (by linarith) ht'
    have hg0 : 0 ≤ g 0 :=
      ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
    have hg0' : g 0 = -(Δ ⬝ᵥ Δ + δ * δ) := by
      simp only [hg, zero_smul, add_zero, zero_mul, dotProduct_neg]
      rw [← hΔ, ← hδ]
      ring
    rw [hg0'] at hg0
    have hΔn := self_nonneg Δ
    have hΔ0 : Δ ⬝ᵥ Δ = 0 := by nlinarith [mul_self_nonneg δ]
    have hδ0 : δ = 0 := by nlinarith [mul_self_nonneg δ]
    have hΔ0' : Δ = 0 := dotProduct_self_eq_zero.1 hΔ0
    refine Or.inl ⟨hσ, ?_⟩
    show (w, κ) = (M *ᵥ x + σ • q, -(x ⬝ᵥ (M *ᵥ x)) / σ - x ⬝ᵥ q)
    rw [Prod.mk.injEq]
    exact ⟨sub_eq_zero.1 hΔ0', sub_eq_zero.1 hδ0⟩

end RRAux_HomogLCP_Embed_lemma_4_4

open Matrix in
open HomogLCP.Embed in
theorem solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMaximalMonotoneOp (embQ M q) := by
  refine ⟨RRAux_HomogLCP_Embed_lemma_4_4.mono M q hM, fun T' hT' hsub => ?_⟩
  refine Set.Subset.antisymm (fun a ha => ?_) hsub
  obtain ⟨⟨x, σ⟩, w, κ⟩ := a
  exact RRAux_HomogLCP_Embed_lemma_4_4.key_max M q hM x w σ κ
    (fun b hb => hT' _ ha b (hsub hb))

#print axioms solution
