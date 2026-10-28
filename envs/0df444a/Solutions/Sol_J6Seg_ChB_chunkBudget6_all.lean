-- Prove2me | solution 1 for J6Seg.ChB.chunkBudget6_all
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:50:05.510399+00:00
-- url     : https://prove2.me/submissions/15761ce3-a64a-435b-b664-dea571b72f21

import Definitions.Def_IntMul_Kappa_R6_Defs70
import Theorems.Thm_J6Seg_Side_axNum_ev
import Theorems.Thm_J6Seg_chunkTabBnd6_all
import Theorems.Thm_J6Seg_ChB_chunk_facts
import Theorems.Thm_J6Seg_ChB_chunk_cost_nat
import Theorems.Thm_J6Seg_ChB_cY_le

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntMul NLogN NLogN.KIL NLogN.KFB IntMul.Kappa.R6 J6Seg J6Seg.KR
open J6Seg.ChB J6Seg.Side J6Seg.Ax J6Seg.AxCh

private theorem Kch_nonneg (P : Prm) (ap : AxPlan6) : 0 ≤ Kch P ap := by
  unfold Kch C1 K3
  positivity

private theorem dl_le_Ncost6 (P : Prm) (n : ℕ) : (dP6 P n : ℝ) + ℓP6 P n ≤ Ncost6 P n := by
  unfold Ncost6 Ncost6R
  have hp1 : (1 : ℝ) ≤ pP6 P n := by
    have : 1 ≤ pP6 P n := by unfold pP6; have := b'P6_pos P n; omega
    exact_mod_cast this
  have hp0 : (0 : ℝ) ≤ pP6 P n := by linarith
  have hd : (0 : ℝ) ≤ dP6 P n := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ ℓP6 P n := Nat.cast_nonneg _
  have t1 : 0 ≤ (ℓP6 P n : ℝ) * (dP6 P n : ℝ) ^ P.lamp := mul_nonneg hl (Real.rpow_nonneg hd _)
  have t2 : 0 ≤ (dP6 P n : ℝ) * (pP6 P n : ℝ) ^ P.δ := mul_nonneg hd (Real.rpow_nonneg hp0 _)
  have t3 : 0 ≤ Real.logb 2 (pP6 P n) := Real.logb_nonneg (by norm_num) hp1
  have t4 : 0 ≤ (pP6 P n : ℝ) ^ P.δ := Real.rpow_nonneg hp0 _
  have t5 : 0 ≤ (ℓP6 P n : ℝ) * ((dP6 P n : ℝ) * Real.log (pP6 P n)) ^ P.τ :=
    mul_nonneg hl (Real.rpow_nonneg (mul_nonneg hd (Real.log_nonneg hp1)) _)
  linarith

/-- `ChunkTabBnd6` is definitionally the existential of `TabAt`. -/
private theorem tabAt_of (P : Prm) (h : ChunkTabBnd6 P) :
    ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → ∀ src : ℕ → ℕ, SrcOK6 P n src →
      ∀ D : ℕ, dP6 P n = D + 1 → ∀ k ≤ D, J6Seg.Ax.TabAt P n src k := h

private theorem chunk_budget_at {P : Prm} {n : ℕ} {src : ℕ → ℕ} {D k : ℕ} (ap : AxPlan6)
    (h : AxNum P n src D k) (hT : J6Seg.Ax.TabAt P n src k) (hc : ChunkPlan6 ap) (hcb : ChunkPlanB ap)
    (hD : dP6 P n = D + 1) :
    ChunkBudgetAt P ap n src D k (Kch P ap * cU6 P n 2 / (D + 1)) := by
  refine ⟨_, _, _, _, _, chunk_facts ap h hT hc hcb, ?_⟩
  have hN := chunk_cost_nat ap h
  have hY := cY_le ap h
  have hNR := (Nat.cast_le (α := ℝ)).2 hN
  push_cast at hNR
  have hdR : ((D : ℝ) + 1) = (dP6 P n : ℝ) := by rw [hD]; push_cast; ring
  have hcU : cU6 P n 2 = ((TP6 P n : ℝ) * pP6 P n) * Ncost6 P n *
      (Real.log (IntMul.lg n) + 1) ^ 2 := rfl
  rw [hdR, hcU]
  have hd0 : (0 : ℝ) < dP6 P n := by have := h.d1; exact_mod_cast this
  rw [le_div_iff₀ hd0]
  have hdl := dl_le_Ncost6 P n
  have hℓ0 : (0 : ℝ) ≤ ℓP6 P n := Nat.cast_nonneg _
  have hNcd : (dP6 P n : ℝ) ≤ Ncost6 P n := by linarith
  have hT0 : (0 : ℝ) ≤ TP6 P n := Nat.cast_nonneg _
  have hK0 := Kch_nonneg P ap
  have hp0 : (0 : ℝ) ≤ pP6 P n := Nat.cast_nonneg _
  set X := (kerC (cCk P n src k ap) (cBk P n src k ap) (2 ^ axfC6 P n) (axpost6 P n D k) (cLc P n)
      (axnc6 P n k) (tabsT (axTC6 P n src k ap) (axnc6 P n k)).length (axpre6 P n D k)
      (2 * (axpre6 P n D k * axnc6 P n k * axpost6 P n D k * 2 ^ axfC6 P n)) : ℝ) with hX
  have h1 : X ≤ (TP6 P n : ℝ) * (Kch P ap * ((pP6 P n : ℝ) * (Real.log (IntMul.lg n) + 1) ^ 2)) :=
    hNR.trans (mul_le_mul_of_nonneg_left hY hT0)
  have hQ0 : (0 : ℝ) ≤ (TP6 P n : ℝ) * (Kch P ap * ((pP6 P n : ℝ) * (Real.log (IntMul.lg n) + 1) ^ 2)) :=
    mul_nonneg hT0 (mul_nonneg hK0 (mul_nonneg hp0 (sq_nonneg _)))
  calc X * (dP6 P n : ℝ) ≤ ((TP6 P n : ℝ) * (Kch P ap * ((pP6 P n : ℝ) *
        (Real.log (IntMul.lg n) + 1) ^ 2))) * Ncost6 P n :=
        mul_le_mul h1 hNcd hd0.le hQ0
    _ = Kch P ap * (((TP6 P n : ℝ) * pP6 P n) * Ncost6 P n * (Real.log (IntMul.lg n) + 1) ^ 2) := by
        ring

/-- `ChunkBudget6` from `axNum_ev`, Open `chunkTabBnd6_all`, and the per-axis budget. -/
theorem solution (P : Prm) (hP : P.Ok) (ap : AxPlan6) (hc : ChunkPlan6 ap)
    (hcb : ChunkPlanB ap) : ChunkBudget6 P ap := by
  obtain ⟨n₀, hN⟩ := axNum_ev P hP
  obtain ⟨n₁, hT⟩ := tabAt_of P (chunkTabBnd6_all P hP)
  exact ⟨Kch P ap, 2, max n₀ n₁, Kch_nonneg P ap, fun n hn src hs D hD k hk =>
    chunk_budget_at ap (hN n (le_of_max_le_left hn) src hs D hD k hk)
      (hT n (le_of_max_le_right hn) src hs D hD k hk) hc hcb hD⟩

end
