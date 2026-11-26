-- Prove2me | solution 1 for HomogLCP.Embed.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:48:51.502797+00:00
-- url     : https://prove2.me/submissions/126461d7-fbf8-4ec6-aa79-8a94170a347d

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting
namespace HomogLCP.Embed

open Matrix

/-- Lemma 4.3, pp. 9–10: the operator `ℐ` is monotone. -/
theorem _root_.solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMonotoneOp (embI M q) := by
  have hpsd : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    intro v
    have h := hM.dotProduct_mulVec_nonneg v
    rw [star_trivial, Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm v (v ᵥ* M), ← Matrix.dotProduct_mulVec] at h
    linarith
  have hexp : ∀ (s t : ℝ) (u v : Fin d → ℝ), (s • u + t • v) ⬝ᵥ (M *ᵥ (s • u + t • v))
      = s^2 * (u ⬝ᵥ (M *ᵥ u)) + s*t*(u ⬝ᵥ (M *ᵥ v) + v ⬝ᵥ (M *ᵥ u)) + t^2 * (v ⬝ᵥ (M *ᵥ v)) := by
    intro s t u v
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hFF : ∀ a ∈ embF M q, ∀ b ∈ embF M q, 0 ≤ pair (a.2 - b.2) (a.1 - b.1) := by
    rintro ⟨⟨z, τ⟩, u⟩ ⟨hτ, hu⟩ ⟨⟨w, κ⟩, v⟩ ⟨hκ, hv⟩
    simp only at hτ hu hκ hv
    subst hu hv
    have h := hpsd (κ • z + (-τ) • w)
    rw [hexp] at h
    have e : pair ((M *ᵥ z + τ • q, -(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - (M *ᵥ w + κ • q, -(w ⬝ᵥ (M *ᵥ w)) / κ - w ⬝ᵥ q))
        ((z, τ) - (w, κ)) = (κ^2 * (z ⬝ᵥ (M *ᵥ z)) + κ*(-τ)*(z ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ z)) + (-τ)^2 * (w ⬝ᵥ (M *ᵥ w))) / (τ*κ) := by
      simp only [pair, Prod.mk_sub_mk, sub_dotProduct, dotProduct_sub, add_dotProduct,
        smul_dotProduct, smul_eq_mul, dotProduct_comm (M *ᵥ z), dotProduct_comm (M *ᵥ w), dotProduct_comm q]
      field_simp
      ring
    simp only
    rw [e]
    exact div_nonneg h (mul_pos hτ hκ).le
  have hII : ∀ a ∈ embI M q, ∀ b ∈ embI M q, 0 ≤ pair (a.2 - b.2) (a.1 - b.1) := by
    rintro ⟨⟨z, τ⟩, u1, u2⟩ ⟨h1, h2, h3, h4⟩ ⟨⟨w, κ⟩, v1, v2⟩ ⟨k1, k2, k3, k4⟩
    simp only at h1 h2 h3 h4 k1 k2 k3 k4
    subst h1 k1 h3 k3
    have h := hpsd (z - w)
    simp only [pair, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, sub_self, mul_zero, add_zero]
    rw [← Matrix.mulVec_sub, dotProduct_comm]
    exact h
  have hFI : ∀ a ∈ embF M q, ∀ b ∈ embI M q, 0 ≤ pair (a.2 - b.2) (a.1 - b.1) := by
    rintro ⟨⟨z, τ⟩, u⟩ ⟨hτ, hu⟩ ⟨⟨w, κ⟩, v1, v2⟩ ⟨k1, k2, k3, k4⟩
    simp only at hτ hu k1 k2 k3 k4
    subst hu k1 k3
    have hcross : z ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ z) = 0 := by
      set c := z ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ z) with hc
      set A := z ⬝ᵥ (M *ᵥ z) with hA
      have key : ∀ t : ℝ, 0 ≤ t * c + t^2 * A := by
        intro t
        have h := hpsd ((1:ℝ) • w + t • z)
        rw [hexp, k2] at h
        rw [hc, hA]; nlinarith
      have hA0 : 0 ≤ A := hpsd z
      have h1 := key (-c / (A + 1))
      have hpos : 0 < A + 1 := by linarith
      have e : -c / (A + 1) * c + (-c / (A + 1)) ^ 2 * A = -(c^2) / (A+1)^2 := by
        field_simp; ring
      rw [e, le_div_iff₀ (by positivity), zero_mul] at h1
      have : c^2 = 0 := le_antisymm (by linarith) (sq_nonneg c)
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    have e : pair ((M *ᵥ z + τ • q, -(z ⬝ᵥ (M *ᵥ z)) / τ - z ⬝ᵥ q) - (M *ᵥ w, v2)) ((z, τ) - (w, (0:ℝ)))
        = -(z ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ z)) + τ * (-(w ⬝ᵥ q) - v2) + w ⬝ᵥ (M *ᵥ w) := by
      simp only [pair, Prod.mk_sub_mk, sub_dotProduct, dotProduct_sub, add_dotProduct,
        smul_dotProduct, smul_eq_mul, dotProduct_comm (M *ᵥ z), dotProduct_comm (M *ᵥ w), dotProduct_comm q, sub_zero]
      field_simp
      ring
    simp only
    rw [e, hcross, k2]
    have := mul_nonneg hτ.le (sub_nonneg.2 k4)
    linarith
  have hsym : ∀ a b : ((Fin d → ℝ) × ℝ) × ((Fin d → ℝ) × ℝ), pair (a.2 - b.2) (a.1 - b.1) = pair (b.2 - a.2) (b.1 - a.1) := by
    intro a b
    rw [← neg_sub b.2 a.2, ← neg_sub b.1 a.1]
    unfold pair
    simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg, neg_neg, neg_mul_neg]
  exact hII


end HomogLCP.Embed

