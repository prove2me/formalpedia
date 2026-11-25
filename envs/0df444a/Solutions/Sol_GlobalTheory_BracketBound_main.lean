-- Prove2me | solution 1 for GlobalTheory.BracketBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:59.329449+00:00
-- url     : https://prove2.me/submissions/ebb8e213-a732-4f88-a830-e43aea818ab2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SideSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdLeOfInterlacingPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InterlacedShiftedDistanceBracketBound
import Theorems.Thm_GlobalTheory_CloudProd_main
import Theorems.Thm_GlobalTheory_prod_le_of_interlacing_pairing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.BracketBound
namespace GlobalTheory.BracketBound
theorem _root_.solution : ∀ (k r l : ℕ) (b c Y e : ℝ) (lam v : ℕ → ℝ), 1 ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |Y| ≤ b → 0 ≤ e → e ≤ 1 → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → ∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k r l b c Y e lam v hk hc hcb hkb hY he0 he1 hlam hgap hint hW
  have hb3 : 3 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h3b : 3 * b ≤ b ^ 2 := by nlinarith
  have ha0 : ∀ s, 0 ≤ |Y + e + lam s| + c := fun s => by positivity
  have ha1 : ∀ s, |Y + e + lam s| + c ≤ |lam s + Y| + 1 + c := fun s => by
    have h1 : |Y + e + lam s| ≤ |lam s + Y| + |e| := by
      have : Y + e + lam s = (lam s + Y) + e := by ring
      rw [this]; exact abs_add_le _ _
    rw [abs_of_nonneg he0] at h1
    linarith
  have ha2 : ∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |Y + e + lam s| + c ≤ 3 * b := fun s hs => by
    have h1 := ha1 s
    have h2 := abs_add_le (lam s) Y
    have h3 := hlam s hs
    linarith
  have hsplit : Finset.Icc 1 (k + 2 * r + 1) = Finset.Icc 1 (k - 1) ∪ Finset.Icc k (k + 2 * r + 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (k - 1)) (Finset.Icc k (k + 2 * r + 1)) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_Icc]; omega
  have hWp : 0 ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  have hpair := GlobalTheory.prod_le_of_interlacing_pairing k l c (3 * b) Y lam v (fun s => |Y + e + lam s| + c)
    (by linarith) (by linarith) (fun s h1 h2 => by have := hgap s h1 h2; linarith) hint hW
    (fun s hs => ⟨ha0 s, ha1 s, ha2 s (by rw [hsplit]; exact Finset.mem_union_left _ hs)⟩)
  have hcloud := GlobalTheory.CloudProd.main k c (-Y) lam hk hc hgap
  simp only [sub_neg_eq_add] at hcloud
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : ((2 + c) * (k : ℝ)) ^ 2 ≤ b ^ 4 := by
    have h1 : (2 + c) * (k : ℝ) ≤ b * b := mul_le_mul (by linarith) hkb hk0 hb0
    calc ((2 + c) * (k : ℝ)) ^ 2 ≤ (b * b) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = b ^ 4 := by ring
  have hR0 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
    Finset.prod_nonneg fun s _ => by positivity
  have hC : ∏ s ∈ Finset.Icc 1 (k - 1), (|Y + e + lam s| + c) ≤
      b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    refine hpair.trans (mul_le_mul_of_nonneg_right ?_ hWp)
    exact mul_le_mul h3b (hcloud.trans h4) hR0 (by positivity)
  have hN : ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ (b ^ 2) ^ (2 * r + 2) := by
    calc ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c)
        ≤ ∏ _s ∈ Finset.Icc k (k + 2 * r + 1), b ^ 2 :=
          Finset.prod_le_prod (fun s _ => ha0 s) (fun s hs =>
            (ha2 s (by rw [hsplit]; exact Finset.mem_union_right _ hs)).trans h3b)
      _ = (b ^ 2) ^ (2 * r + 2) := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 1; omega
  rw [hsplit, Finset.prod_union hdisj]
  calc _ ≤ (b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i|) * (b ^ 2) ^ (2 * r + 2) :=
        mul_le_mul hC hN (Finset.prod_nonneg fun s _ => ha0 s) (by positivity)
    _ = b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by ring
end GlobalTheory.BracketBound
