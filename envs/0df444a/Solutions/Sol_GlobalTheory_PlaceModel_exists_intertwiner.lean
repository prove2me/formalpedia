-- Prove2me | solution 1 for GlobalTheory.PlaceModel.exists_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:29:27.310624+00:00
-- url     : https://prove2.me/submissions/f5046723-56e4-413c-8135-f4e1fdf2cf57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_trans
import Theorems.Thm_GlobalTheory_PlaceModel_wave_modul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_zero
import Theorems.Thm_GlobalTheory_PlaceModel_exists_map_wave
import Theorems.Thm_GlobalTheory_PlaceModel_ind_nsmul_mem
import Theorems.Thm_GlobalTheory_PlaceModel_mem_of_finite_cosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', ρ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, T (ind L) = f₀ ∧ ∀ Φ : G → ℂ, (∀ t, Φ t ≠ 0 → t ∈ X) → ∀ k : ℕ, 0 < k →
      (∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) → (∀ t, Φ t ≠ 0 → k • t ∈ L) →
      (∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ) := by
  classical
  obtain ⟨T, hT⟩ := exists_map_wave h hL hL' hLL' hY ρ ρX ρY ρXY f₀ hf hf'

  have htrans : ∀ Φ ∈ waveSpan χ X Y L, ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ) := by
    intro Φ hΦ x hx
    unfold waveSpan at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Ψ hΨ =>
      obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := hΨ
      rw [wave_trans, hT _ (X.add_mem hx hx₀) _ hy₀, hT _ hx₀ _ hy₀, ρX x hx x₀ hx₀]
    | zero =>
      have e : (fun t => (0 : G → ℂ) (t + x)) = 0 := rfl
      rw [e]
      simp only [map_zero]
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      have e : (fun t => (Φ₁ + Φ₂) (t + x)) = (fun t => Φ₁ (t + x)) + (fun t => Φ₂ (t + x)) := rfl
      rw [e]
      simp only [map_add, h₁, h₂]
    | smul a Φ₁ _ h₁ =>
      have e : (fun t => (a • Φ₁) (t + x)) = a • (fun t => Φ₁ (t + x)) := rfl
      rw [e]
      simp only [map_smul, h₁]

  have hmod : ∀ Φ ∈ waveSpan χ X Y L, ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ) := by
    intro Φ hΦ y hy
    unfold waveSpan at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Ψ hΨ =>
      obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := hΨ
      rw [wave_modul h, map_smul, hT _ hx₀ _ (Y.add_mem hy hy₀), hT _ hx₀ _ hy₀,
        ← ρY y hy y₀ hy₀, ρXY x₀ hx₀ y hy, smul_smul, h.neg_mul, one_smul]
    | zero =>
      have e : (fun t => χ t y * (0 : G → ℂ) t) = 0 := by
        funext t
        simp
      rw [e]
      simp only [map_zero]
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      have e : (fun t => χ t y * (Φ₁ + Φ₂) t) =
          (fun t => χ t y * Φ₁ t) + (fun t => χ t y * Φ₂ t) := by
        funext t
        simp [mul_add]
      rw [e]
      simp only [map_add, h₁, h₂]
    | smul a Φ₁ _ h₁ =>
      have e : (fun t => χ t y * (a • Φ₁) t) = a • (fun t => χ t y * Φ₁ t) := by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      simp only [map_smul, h₁]
  refine ⟨T, ?_, fun Φ hΦX k hk hinv hsupp => ?_⟩
  · rw [← wave_zero (χ := χ) (L := L) h, hT 0 X.zero_mem 0 Y.zero_mem, hf 0 L.zero_mem,
      hf 0 L.zero_mem]
  obtain ⟨R, hR, hcov⟩ := hfin k hk
  have hKmem := ind_nsmul_mem h hL hL' hLL' hX (dX k hk) (dY k hk) R hR hcov

  let σ : G → G := fun r => if hr : ∃ s, k • s = r then hr.choose else 0
  let P : Finset G := (hR.toFinset ×ˢ hR.toFinset).image fun p => σ p.1 + p.2
  have hΦ : Φ ∈ waveSpan χ X Y L := by
    refine mem_of_finite_cosets hKmem P Φ hΦX ?_ ?_
    · intro u hu t
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hu
      exact hinv w hw t
    · intro t ht
      obtain ⟨r, hr, u, hu, hku⟩ := hcov _ (hsupp t ht)
      have hex : ∃ s, k • s = r := ⟨t - u, by rw [smul_sub, hku, add_sub_cancel_right]⟩
      have hσ : σ r = t - u := by
        apply tf k hk
        simp only [σ, dif_pos hex]
        rw [hex.choose_spec, smul_sub, hku, add_sub_cancel_right]
      obtain ⟨r', hr', u', hu', rfl⟩ := hcov u hu
      refine ⟨σ r + r', Finset.mem_image.mpr ⟨(r, r'), ?_, rfl⟩, k • u',
        AddSubgroup.mem_map.mpr ⟨u', hu', rfl⟩, ?_⟩
      · simp [hr, hr']
      · rw [hσ]
        abel
  exact ⟨fun x hx => htrans Φ hΦ x hx, fun y hy => hmod Φ hΦ y hy⟩
end GlobalTheory.PlaceModel
