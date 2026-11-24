-- Prove2me | solution 1 for GlobalTheory.SchrodExist.exists_intertwiner_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:16.534801+00:00
-- url     : https://prove2.me/submissions/c7ddc414-9db7-482d-a103-f57753bab82d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul
import Theorems.Thm_GlobalTheory_PlaceModel_exists_map_wave
import Theorems.Thm_GlobalTheory_PlaceModel_ind_nsmul_mem
import Theorems.Thm_GlobalTheory_PlaceModel_mem_of_finite_cosets
import Theorems.Thm_GlobalTheory_PlaceModel_wave_modul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_trans
import Theorems.Thm_GlobalTheory_PlaceModel_wave_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel
namespace GlobalTheory.SchrodExist
theorem _root_.solution {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    {χ : G → G → ℂ} {X Y L L' : AddSubgroup G} (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
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
      (∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧ (∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ)) ∧
      T Φ ∈ Submodule.span ℂ {v | ∃ x ∈ X, ∃ y ∈ Y, v = ρ x (ρ y f₀)} := by
  obtain ⟨T, hT⟩ := exists_map_wave h hL hL' hLL' hY ρ ρX ρY ρXY f₀ hf hf'
  have h0L : (0 : G) ∈ L := L.zero_mem
  have hρ0 : ρ 0 f₀ = f₀ := hf 0 h0L
  have hind : T (ind L) = f₀ := by
    rw [← wave_zero (L := L) h, hT 0 (hL h0L) 0 (hL' L'.zero_mem), hρ0, hρ0]
  refine ⟨T, hind, ?_⟩
  intro Φ hΦX k hk hΦL hΦk
  have hmem : Φ ∈ waveSpan χ X Y L := by
    obtain ⟨R₁, hR₁, hR₁L⟩ := hfin k hk
    have hK := ind_nsmul_mem h hL hL' hLL' hX (dX k hk) (dY k hk) R₁ hR₁ hR₁L
    obtain ⟨R, hR, hRL⟩ := hfin (k * k) (Nat.mul_pos hk hk)
    have hpre : ∀ r ∈ R, ∃ s : G, (∃ t, k • t = r) → k • s = r := fun r _ => by
      by_cases hr : ∃ t, k • t = r
      · obtain ⟨t, ht⟩ := hr
        exact ⟨t, fun _ => ht⟩
      · exact ⟨0, fun h' => absurd h' hr⟩
    choose! s hs using hpre
    refine mem_of_finite_cosets hK (hR.image s).toFinset Φ hΦX ?_ ?_
    · intro u hu t
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hu
      simpa using hΦL l hl t
    · intro t ht
      obtain ⟨r, hr, u, hu, hkt⟩ := hRL (k • t) (hΦk t ht)
      have hex : ∃ t', k • t' = r := ⟨t - k • u, by rw [smul_sub, smul_smul, hkt, add_sub_cancel_right]⟩
      refine ⟨s r, ?_, k • u, AddSubgroup.mem_map.2 ⟨u, hu, by simp⟩, ?_⟩
      · simp only [Set.Finite.mem_toFinset, Set.mem_image]
        exact ⟨r, hr, rfl⟩
      · apply tf k hk
        show k • t = k • (s r + k • u)
        rw [smul_add, hs r hr hex, smul_smul]
        exact hkt
  have key : ∀ Ψ ∈ waveSpan χ X Y L, (∀ x ∈ X, T (fun t => Ψ (t + x)) = ρ x (T Ψ)) ∧
      (∀ y ∈ Y, T (fun t => χ t y * Ψ t) = ρ y (T Ψ)) ∧
      T Ψ ∈ Submodule.span ℂ {v | ∃ x ∈ X, ∃ y ∈ Y, v = ρ x (ρ y f₀)} := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem Ψ hΨ =>
      obtain ⟨x', hx', y', hy', rfl⟩ := hΨ
      refine ⟨fun x hx => ?_, fun y hy => ?_, Submodule.subset_span ⟨x', hx', y', hy', hT x' hx' y' hy'⟩⟩
      · rw [wave_trans, hT _ (X.add_mem hx hx') _ hy', hT _ hx' _ hy', ρX _ hx _ hx']
      · rw [wave_modul h, map_smul, hT _ hx' _ (Y.add_mem hy hy'), hT _ hx' _ hy', ← ρY _ hy _ hy',
          ρXY x' hx' y hy, smul_smul, h.neg_mul, one_smul]
    | zero =>
      refine ⟨fun x _ => ?_, fun y _ => ?_, by rw [map_zero]; exact zero_mem _⟩
      · have e : (fun t => (0 : G → ℂ) (t + x)) = 0 := rfl
        rw [e, map_zero, map_zero]
      · have e : (fun t => χ t y * (0 : G → ℂ) t) = 0 := by
          funext t
          simp
        rw [e, map_zero, map_zero]
    | add Ψ₁ Ψ₂ _ _ ih₁ ih₂ =>
      refine ⟨fun x hx => ?_, fun y hy => ?_, by rw [map_add]; exact add_mem ih₁.2.2 ih₂.2.2⟩
      · have e : (fun t => (Ψ₁ + Ψ₂) (t + x)) = (fun t => Ψ₁ (t + x)) + fun t => Ψ₂ (t + x) := rfl
        rw [e, map_add, map_add, map_add, ih₁.1 x hx, ih₂.1 x hx]
      · have e : (fun t => χ t y * (Ψ₁ + Ψ₂) t) = (fun t => χ t y * Ψ₁ t) + fun t => χ t y * Ψ₂ t := by
          funext t
          simp [mul_add]
        rw [e, map_add, map_add, map_add, ih₁.2.1 y hy, ih₂.2.1 y hy]
    | smul c Ψ _ ih =>
      refine ⟨fun x hx => ?_, fun y hy => ?_, by rw [map_smul]; exact Submodule.smul_mem _ c ih.2.2⟩
      · have e : (fun t => (c • Ψ) (t + x)) = c • fun t => Ψ (t + x) := rfl
        rw [e, map_smul, map_smul, map_smul, ih.1 x hx]
      · have e : (fun t => χ t y * (c • Ψ) t) = c • fun t => χ t y * Ψ t := by
          funext t
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, map_smul, map_smul, map_smul, ih.2.1 y hy]
  exact key Φ hmem
end GlobalTheory.SchrodExist
