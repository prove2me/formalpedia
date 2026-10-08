-- Prove2me | solution 1 for LemkeLCP.Existence.theorem_4_ray_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:15:40.291031+00:00
-- url     : https://prove2.me/submissions/22fb449d-c899-4a90-8b27-84df8f219345

import Mathlib
import Definitions.Def_LemkeLCP_Existence_Setting
open Matrix


namespace LemkeLCP.Existence

theorem rs_nonneg_of_ray (a b : ℝ) (h : ∀ θ : ℝ, 0 ≤ θ → 0 ≤ a + θ * b) : 0 ≤ b := by
  by_contra hb
  have hb : b < 0 := not_le.mp hb
  have := h ((|a| + 1) / (-b)) (div_nonneg (by positivity) (by linarith))
  have h2 : (|a| + 1) / (-b) * b = -(|a| + 1) := by
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
  have := le_abs_self a
  linarith

theorem rs_core {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hM : CopositivePlus M)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    (zb0 = 0 ∧ IsEquilibriumPoint M q zb) ∨ (0 < zb0 ∧ Z M q = ∅) := by
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
  have hC : u ⬝ᵥ (M *ᵥ u) + u0 = 0 := by nlinarith
  have hA : zb ⬝ᵥ (M *ᵥ zb + (fun _ => zb0) - q) = 0 := by
    have := h0; simp at this; simpa using this
  have hB : zb ⬝ᵥ (M *ᵥ u) + zb ⬝ᵥ (fun _ => u0) + u ⬝ᵥ (M *ᵥ zb + (fun _ => zb0) - q) = 0 := by
    nlinarith
  -- nonnegativity
  have hz : 0 ≤ zb := fun i => by simpa using (hray 0 le_rfl).1.1 i
  have hz0 : 0 ≤ zb0 := by simpa using (hray 0 le_rfl).1.2.1
  have hw : 0 ≤ M *ᵥ zb + (fun _ => zb0) - q := by simpa using (hray 0 le_rfl).1.2.2
  have hu_nn : 0 ≤ u := fun i => by
    apply rs_nonneg_of_ray (zb i) (u i)
    intro θ hθ
    simpa using (hray θ hθ).1.1 i
  have hu0 : 0 ≤ u0 := by
    apply rs_nonneg_of_ray zb0 u0
    intro θ hθ
    simpa using (hray θ hθ).1.2.1
  have hMui : ∀ i, 0 ≤ (M *ᵥ u) i + u0 := fun i => by
    apply rs_nonneg_of_ray ((M *ᵥ zb) i + zb0 - q i) ((M *ᵥ u) i + u0)
    intro θ hθ
    have := (hray θ hθ).1.2.2 i
    simp [mulVec_add, mulVec_smul] at this
    linarith
  obtain ⟨hcp1, hcp2⟩ := hM u hu_nn
  have hq0 : u ⬝ᵥ (M *ᵥ u) = 0 := by linarith
  have hu00 : u0 = 0 := by linarith
  have hsym := hcp2 hq0
  have hMu' : 0 ≤ M *ᵥ u := fun i => by have := hMui i; rw [hu00] at this; simpa using this
  have hz1 : zb ⬝ᵥ (fun _ : ι => u0) = 0 := by simp [dotProduct, hu00]
  have swap : ∀ y : ι → ℝ, ∀ v : ι → ℝ, Mᵀ *ᵥ v = -(M *ᵥ v) → v ⬝ᵥ (M *ᵥ y) = -(y ⬝ᵥ (M *ᵥ v)) := by
    intro y v hv
    rw [dotProduct_mulVec, ← mulVec_transpose, hv, neg_dotProduct, dotProduct_comm (M *ᵥ v) y]
  have hTu : Mᵀ *ᵥ u = -(M *ᵥ u) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsym
  rcases hz0.eq_or_lt with h | h
  · left
    subst h
    refine ⟨rfl, ⟨?_, ?_⟩⟩
    · refine ⟨hz, ?_⟩
      intro i
      have := hw i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at this
      show (0:ℝ) ≤ (M *ᵥ zb - q) i
      simp only [Pi.sub_apply]
      linarith
    · have e : M *ᵥ zb + (fun _ : ι => (0:ℝ)) - q = M *ᵥ zb - q := by ext i; simp
      rw [e] at hA; exact hA
  · right
    refine ⟨h, ?_⟩
    have hcz : u ⬝ᵥ (fun _ : ι => zb0) = zb0 := by simp [dotProduct, ← Finset.sum_mul, hu]
    have hqu : u ⬝ᵥ q = zb0 := by
      have e1 := swap zb u hTu
      have e1' : u ⬝ᵥ (M *ᵥ zb) = -(zb ⬝ᵥ (M *ᵥ u)) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hTu, neg_dotProduct, dotProduct_comm (M *ᵥ u) zb]
      have e2 : u ⬝ᵥ (M *ᵥ zb + (fun _ => zb0) - q) = u ⬝ᵥ (M *ᵥ zb) + zb0 - u ⬝ᵥ q := by
        rw [dotProduct_sub, dotProduct_add, hcz]
      linarith
    ext z
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hzz
    obtain ⟨hz1', hz2⟩ := hzz
    have hz2' : q ≤ M *ᵥ z := fun i => by have := hz2 i; simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢; linarith
    have h3 : u ⬝ᵥ q ≤ u ⬝ᵥ (M *ᵥ z) := dotProduct_le_dotProduct_of_nonneg_left hz2' hu_nn
    have h4 : u ⬝ᵥ (M *ᵥ z) = -(z ⬝ᵥ (M *ᵥ u)) := swap z u hTu
    have h5 : 0 ≤ z ⬝ᵥ (M *ᵥ u) := dotProduct_nonneg_of_nonneg hz1' hMu'
    linarith
end LemkeLCP.Existence

open LemkeLCP.Existence


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (q : ι → ℝ) (hM : CopositivePlus M)
    (zb u : ι → ℝ) (zb0 u0 : ℝ)
    (hray : ∀ θ : ℝ, 0 ≤ θ → (zb + θ • u, zb0 + θ * u0) ∈ Z0star M q)
    (hu : ∑ i, u i = 1) :
    (zb0 = 0 ∧ IsEquilibriumPoint M q zb) ∨ (0 < zb0 ∧ Z M q = ∅) := by
  exact rs_core M q hM zb u zb0 u0 hray hu
