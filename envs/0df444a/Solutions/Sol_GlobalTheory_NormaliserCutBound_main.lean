-- Prove2me | solution 1 for GlobalTheory.NormaliserCutBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:02:25.003281+00:00
-- url     : https://prove2.me/submissions/ea134162-757c-4bab-8273-8c1efae3957c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdFinEqProdIcc
import Theorems.Thm_GlobalTheory_NormaliserCutBound_prod_fin_eq_prod_Icc
import Theorems.Thm_GlobalTheory_NormaliserCutBound_qC_re
import Theorems.Thm_Formalism_FourierDecayAlt_P_q_positive_interlacing
import Theorems.Thm_GlobalTheory_BracketBound_main
import Theorems.Thm_GlobalTheory_CloudProd_main
import Theorems.Thm_GlobalTheory_LamSize_main
import Theorems.Thm_GlobalTheory_two_brackets_le_pow_mul_prod_entries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory GlobalTheory.NormaliserCutBound
namespace GlobalTheory.NormaliserCutBound
theorem _root_.solution : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by
  intro C b c P l lam nn Y hP hC hl hlk hc hcb hkb hu hu' hlam hgap hint hint' hT hT' hnn hcut y hy
  have hcy := hcut y hy
  have hb3 : 3 ≤ b := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = 2 * P.r + P.k + 1 := ⟨_, rfl⟩
  revert lam
  rw [← hn]
  intro lam hlam hgap hint hint' hnn
  let lamN : ℕ → ℝ := fun s => if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
  have hlamN : ∀ s : Fin n, lamN (s.val + 1) = lam s := by
    intro s
    simp [lamN, s.isLt]
  have hlamN' : ∀ (s : ℕ) (h : s - 1 < n), lamN s = lam ⟨s - 1, h⟩ := by
    intro s h
    simp [lamN, h]
  have hn' : P.k + 2 * P.r + 1 = n := by omega
  have hinter : I.Interlaces P.k P.u P.u' P.lo := by
    intro i hi
    have hg := hP.gap i hi
    unfold M.Par.hi at hg
    have h1 := min_le_left (P.u i) (P.u' i)
    have h2 := min_le_right (P.u i) (P.u' i)
    have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> unfold M.Par.lo <;> linarith
  have hint2 : ∀ v : ℕ → ℝ, (∀ s : Fin n, s.val + 2 ≤ P.k →
      (s.val + 1 ≠ l → lam s + 1 / 2 ≤ v (s.val + 1)) ∧
        (s.val + 2 ≠ l → v (s.val + 2) + 1 / 2 ≤ lam s)) →
      ∀ s : ℕ, 1 ≤ s → s + 1 ≤ P.k → (s ≠ l → lamN s + 1 / 2 ≤ v s) ∧
        (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lamN s) := by
    intro v hv s hs hsk
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have ht : t < n := by omega
    have h := hv ⟨t, ht⟩ hsk
    rw [← hlamN ⟨t, ht⟩] at h
    exact h
  have hmain := GlobalTheory.two_brackets_le_pow_mul_prod_entries P.k P.r l b c y lamN P.u P.u' hl hlk hc hcb
    hkb hu hu'
    (by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [hlamN' s (by omega)]
      exact hlam _)
    (by
      intro s hs hsk
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have ht : t < n := by omega
      have ht' : t + 1 < n := by omega
      have h := hgap ⟨t, ht⟩ ⟨t + 1, ht'⟩ rfl (by simp only; omega)
      rw [← hlamN ⟨t, ht⟩, ← hlamN ⟨t + 1, ht'⟩] at h
      exact h)
    (hint2 _ hint) (hint2 _ hint')
    (by
      intro i hi hik
      obtain ⟨h1, h2, h3, h4⟩ := hinter i (Finset.mem_Icc.mpr ⟨hi, hik⟩)
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    hcy
  rw [hn'] at hmain
  have e0 : ∏ s, (|y + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + lamN s| + c) (fun s => by simp only [hlamN])
  have e1 : ∏ s, (|y + 1 + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + 1 + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + 1 + lamN s| + c) (fun s => by simp only [hlamN])
  rw [← e0, ← e1] at hmain
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l y P.T P.T' hl hlk hinter hcy
    hP.T_pos hP.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hP.T_pos hP.T'_pos
  have hqe : I.qpoly P.k P.T P.T' P.u P.u' y = (P.T * P.T') *
      ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| := by
    rw [← abs_of_pos hq]
    unfold I.qpoly
    rw [abs_mul, abs_neg, abs_of_pos hTT, Finset.abs_prod]
  have hsize := (GlobalTheory.LamSize.main C b P.T P.T' P.r 1 hC hb3 (by push_cast; linarith) hT hT').2
  rw [Nat.cast_one, one_mul] at hsize
  have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [qC_re, hqe, ← mul_assoc]
  calc nn y * nn (y + 1) ≤ (∏ s, (|y + lam s| + c)) * ∏ s, (|y + 1 + lam s| + c) :=
        mul_le_mul (hnn y).2 (hnn (y + 1)).2 (hnn (y + 1)).1 ((hnn y).1.trans (hnn y).2)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize hA
end GlobalTheory.NormaliserCutBound
