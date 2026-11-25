-- Prove2me | solution 1 for GlobalTheory.prod_le_of_interlacing_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:35.132255+00:00
-- url     : https://prove2.me/submissions/d69148fd-1de5-48e6-85db-b0fadd56cac4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdLeOfInterlacingPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k l : ℕ) (c B Y : ℝ) (lam v a : ℕ → ℝ), 0 ≤ c → 1 ≤ B → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → (∀ s ∈ Finset.Icc 1 (k - 1), 0 ≤ a s ∧ a s ≤ |lam s + Y| + 1 + c ∧ a s ≤ B) → ∏ s ∈ Finset.Icc 1 (k - 1), a s ≤ B * (∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1)) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k l c B Y lam v a hc hB hlam hv hW ha
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℕ, ∀ s, φ s = if -Y < lam s then s else s + 1 := ⟨_, fun _ => rfl⟩
  have hmem : ∀ s ∈ Finset.Icc 1 (k - 1), φ s ∈ Finset.Icc 1 k := by
    intro s hs
    rw [Finset.mem_Icc] at hs ⊢
    rw [hφ]; split_ifs <;> omega
  have hinj : ∀ s ∈ Finset.Icc 1 (k - 1), ∀ t ∈ Finset.Icc 1 (k - 1), φ s = φ t → s = t := by
    intro s hs t ht h
    rw [Finset.mem_Icc] at hs ht
    rw [hφ, hφ] at h
    split_ifs at h with h1 h2 h2
    · exact h
    · subst h
      have := hlam t ht.1 hs.2
      linarith [not_lt.mp h2]
    · subst h
      have := hlam s hs.1 ht.2
      linarith [not_lt.mp h1]
    · omega
  have hR : ∀ s, 1 ≤ 1 + (1 + c) / max |lam s + Y| 1 := by
    intro s
    have : 0 ≤ (1 + c) / max |lam s + Y| 1 := by positivity
    linarith
  have hkey : ∀ s ∈ Finset.Icc 1 (k - 1), a s ≤ (if φ s = l then B else 1) *
      (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)| := by
    intro s hs
    have hw := hW _ (hmem s hs)
    obtain ⟨h0, h1, h2⟩ := ha s hs
    have hr := hR s
    split_ifs with hl
    · calc a s ≤ B * 1 * 1 := by linarith
        _ ≤ _ := by gcongr
    · rw [Finset.mem_Icc] at hs
      obtain ⟨hv1, hv2⟩ := hv s hs.1 (by omega)
      have hd : |lam s + Y| ≤ |Y + 1 / 2 + v (φ s)| := by
        rw [hφ] at hl ⊢
        split_ifs at hl ⊢ with hy
        · have := hv1 hl
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
        · have := hv2 hl
          have := not_lt.mp hy
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hM : max |lam s + Y| 1 ≤ |Y + 1 / 2 + v (φ s)| := max_le hd hw
      have hM1 : (1 : ℝ) ≤ max |lam s + Y| 1 := le_max_right _ _
      have hM2 : |lam s + Y| ≤ max |lam s + Y| 1 := le_max_left _ _
      have e : (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1
          = max |lam s + Y| 1 + (1 + c) := by
        field_simp
      rw [one_mul]
      calc a s ≤ (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1 := by rw [e]; linarith
        _ ≤ _ := by gcongr
  have hB' : ∏ s ∈ Finset.Icc 1 (k - 1), (if φ s = l then B else 1) ≤ B := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hcard : ((Finset.Icc 1 (k - 1)).filter (fun s => φ s = l)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro s hs t ht
      rw [Finset.mem_filter] at hs ht
      exact hinj s hs.1 t ht.1 (hs.2.trans ht.2.symm)
    calc _ ≤ B ^ 1 := pow_le_pow_right₀ hB hcard
      _ = B := pow_one B
  have hW' : ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)|
      ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    rw [← Finset.prod_image (f := fun i => |Y + 1 / 2 + v i|) (g := φ)
      (fun s hs t ht h => hinj s hs t ht h)]
    have hsub : (Finset.Icc 1 (k - 1)).image φ ⊆ Finset.Icc 1 k := by
      intro i hi
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
      exact hmem s hs
    rw [← Finset.prod_sdiff hsub]
    refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) ?_
    calc (1 : ℝ) = ∏ i ∈ Finset.Icc 1 k \ (Finset.Icc 1 (k - 1)).image φ, 1 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i hi => hW i (Finset.mem_sdiff.mp hi).1)
  calc ∏ s ∈ Finset.Icc 1 (k - 1), a s
      ≤ ∏ s ∈ Finset.Icc 1 (k - 1), ((if φ s = l then B else 1) *
        (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)|) :=
        Finset.prod_le_prod (fun s hs => (ha s hs).1) hkey
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
      have h1 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
        Finset.prod_nonneg fun s _ => zero_le_one.trans (hR s)
      have h2 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)| :=
        Finset.prod_nonneg fun _ _ => abs_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_right hB' h1) hW' h2
        (mul_nonneg (by linarith) h1)
end GlobalTheory
