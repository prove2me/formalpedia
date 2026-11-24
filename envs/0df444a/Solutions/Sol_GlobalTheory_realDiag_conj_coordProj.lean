-- Prove2me | solution 1 for GlobalTheory.realDiag_conj_coordProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:22.250584+00:00
-- url     : https://prove2.me/submissions/2e309e91-9b56-43aa-96f8-4f9e89b171c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoordinateProjectionComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  intro g K ρ hsep T hT j
  classical
  let P : (Fin g → ℝ) → Prop := fun c =>
    ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (c m : ℂ) * v m) = q (T v)
  have hconst : ∀ r : ℝ, P (fun _ => r) := by
    intro r
    refine ⟨(r : ℂ) • LinearMap.id, fun v => ?_⟩
    have h : (fun m ↦ ((r : ℝ) : ℂ) * v m) = r • v := by
      funext m; simp [Complex.real_smul]
    rw [h, map_smul]
    funext m
    simp [Complex.real_smul]
  have hadd : ∀ c d, P c → P d → P (c + d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun v => ?_⟩
    have h : (fun m ↦ (((c + d) m : ℝ) : ℂ) * v m)
        = (fun m ↦ (c m : ℂ) * v m) + (fun m ↦ (d m : ℂ) * v m) := by
      funext m; simp [add_mul]
    rw [h, map_add, h1, h2, LinearMap.add_apply]
  have hmul : ∀ c d, P c → P d → P (c * d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 ∘ₗ q2, fun v => ?_⟩
    calc T (fun m ↦ (((c * d) m : ℝ) : ℂ) * v m)
        = T (fun m ↦ (c m : ℂ) * ((d m : ℂ) * v m)) := by
          congr 1; funext m; simp [mul_assoc]
      _ = q1 (T (fun m ↦ (d m : ℂ) * v m)) := h1 _
      _ = (q1 ∘ₗ q2) (T v) := by rw [h2]; rfl
  have hρ : ∀ a, P (ρ a) := fun a => by
    obtain ⟨M, hM⟩ := hT a
    exact ⟨M, hM⟩
  have haff : ∀ c s t, P c → P (fun m => (c m - s) * t) := by
    intro c s t hc
    have h : (fun m => (c m - s) * t) = (c + (fun _ => -s)) * (fun _ => t) := by
      funext m; simp [sub_eq_add_neg]
    rw [h]; exact hmul _ _ (hadd _ _ hc (hconst _)) (hconst _)
  let f : Fin g → (Fin g → ℝ) := fun k =>
    if h : j ≠ k then
      (fun m => (ρ (Classical.choose (hsep j k h)) m - ρ (Classical.choose (hsep j k h)) k) *
        (ρ (Classical.choose (hsep j k h)) j - ρ (Classical.choose (hsep j k h)) k)⁻¹)
    else 1
  have hf : ∀ k, P (f k) := by
    intro k
    by_cases h : j ≠ k
    · simp only [f, dif_pos h]
      exact haff _ _ _ (hρ _)
    · simp only [f, dif_neg h]
      exact hconst 1
  let δ : Fin g → ℝ := ∏ k ∈ Finset.univ.erase j, f k
  have hδ : P δ := Finset.prod_induction _ P hmul (hconst 1) (fun k _ => hf k)
  have hδj : δ j = 1 := by
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_one
    intro k hk
    have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
    simp only [f, dif_pos hjk]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (Classical.choose_spec (hsep j k hjk)))
  have hδm : ∀ m, m ≠ j → δ m = 0 := by
    intro m hm
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_zero (i := m) (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩)
    have hjm : j ≠ m := fun h => hm h.symm
    simp only [f, dif_pos hjm, sub_self, zero_mul]
  obtain ⟨q, hq⟩ := hδ
  refine ⟨q, fun v => ?_⟩
  rw [← hq]
  congr 1
  funext m
  by_cases hm : m = j
  · subst hm; simp [hδj]
  · simp [hδm m hm, Pi.single_apply, hm]
end GlobalTheory
