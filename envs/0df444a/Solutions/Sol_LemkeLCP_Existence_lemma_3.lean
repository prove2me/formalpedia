-- Prove2me | solution 1 for LemkeLCP.Existence.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:12:38.209766+00:00
-- url     : https://prove2.me/submissions/e29fdbec-f374-4dc8-aad9-d9cf1ba9b8e3

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix


namespace LemkeLCP.Existence

theorem lemma3_core {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    u ⬝ᵥ (M *ᵥ u) + u0 = 0 := by
  have key : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u) ⬝ᵥ (M *ᵥ (zb + θ • u) + (fun _ => zb0 + θ * u0) - q) = 0 :=
    fun θ hθ => (hray θ hθ).2
  have expand : ∀ θ : ℝ, (zb + θ • u) ⬝ᵥ (M *ᵥ (zb + θ • u) + (fun _ => zb0 + θ * u0) - q)
      = zb ⬝ᵥ (M *ᵥ zb + (fun _ => zb0) - q)
        + θ * (zb ⬝ᵥ (M *ᵥ u + (fun _ => u0)) + u ⬝ᵥ (M *ᵥ zb + (fun _ => zb0) - q))
        + θ ^ 2 * (u ⬝ᵥ (M *ᵥ u + (fun _ => u0))) := by
    intro θ
    have h1 : (M *ᵥ (zb + θ • u) + (fun _ => zb0 + θ * u0) - q)
        = (M *ᵥ zb + (fun _ => zb0) - q) + θ • (M *ᵥ u + (fun _ => u0)) := by
      ext i; simp [mulVec_add, mulVec_smul]; ring
    rw [h1, add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul, dotProduct_smul,
      smul_dotProduct]
    simp only [smul_eq_mul]; ring
  have hc : u ⬝ᵥ (fun _ => u0) = u0 := by simp [dotProduct, ← Finset.sum_mul, hu]
  have h0 := key 0 le_rfl
  have h1 := key 1 zero_le_one
  have h2 := key 2 zero_le_two
  rw [expand] at h0 h1 h2
  simp only [dotProduct_add, hc] at h0 h1 h2
  nlinarith
end LemkeLCP.Existence

open LemkeLCP.Existence


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    u ⬝ᵥ (M *ᵥ u) + u0 = 0 := by
  exact lemma3_core M q zb u zb0 u0 hray hu
